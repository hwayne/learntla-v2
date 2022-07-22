"""Allow troubleshootings to be inserted into your documentation.

The troubleshootinglist directive collects all troubleshootings of your project and lists them along
with a backlink to the original location.

Based off todo.py
"""

from typing import Any, Dict, List, Tuple, cast

from docutils import nodes
from docutils.nodes import Element, Node
from docutils.parsers.rst import directives
from docutils.parsers.rst.directives.admonitions import BaseAdmonition

import sphinx
from sphinx import addnodes
from sphinx.application import Sphinx
from sphinx.domains import Domain
from sphinx.environment import BuildEnvironment
from sphinx.errors import NoUri
from sphinx.locale import _, __
from sphinx.util import logging
from sphinx.util.docutils import SphinxDirective, new_document
from sphinx.util.typing import OptionSpec
from sphinx.writers.html import HTMLTranslator

logger = logging.getLogger(__name__)


class troubleshooting_node(nodes.Admonition, nodes.Element):
    pass


class troubleshootinglist(nodes.General, nodes.Element):
    pass


class TroubleshootingDirective(BaseAdmonition, SphinxDirective):
    """
    A troubleshooting entry, displayed (if configured) in the form of an admonition.
    """

    node_class = troubleshooting_node
    has_content = True
    required_arguments = 0
    optional_arguments = 0
    final_argument_whitespace = False
    option_spec: OptionSpec = {
        'class': directives.class_option,
        'name': directives.unchanged,
    }

    def run(self) -> List[Node]:
        if not self.options.get('class'):
            self.options['class'] = ['admonition-troubleshooting']

        (troubleshooting,) = super().run()
        if isinstance(troubleshooting, nodes.system_message):
            return [troubleshooting]
        elif isinstance(troubleshooting, troubleshooting_node):
            troubleshooting.insert(0, nodes.title(text=_('Troubleshooting')))
            troubleshooting['docname'] = self.env.docname
            self.add_name(troubleshooting)
            self.set_source_info(troubleshooting)
            self.state.document.note_explicit_target(troubleshooting)
            return [troubleshooting]
        else:
            raise RuntimeError  # never reached here


class TroubleshootingDomain(Domain):
    name = 'troubleshooting'
    label = 'troubleshooting'

    @property
    def troubleshootings(self) -> Dict[str, List[troubleshooting_node]]:
        return self.data.setdefault('troubleshootings', {})

    def clear_doc(self, docname: str) -> None:
        self.troubleshootings.pop(docname, None)

    def merge_domaindata(self, docnames: List[str], otherdata: Dict) -> None:
        for docname in docnames:
            self.troubleshootings[docname] = otherdata['troubleshootings'][docname]

    def process_doc(self, env: BuildEnvironment, docname: str,
                    document: nodes.document) -> None:
        troubleshootings = self.troubleshootings.setdefault(docname, [])
        for troubleshooting in document.traverse(troubleshooting_node):
            troubleshootings.append(troubleshooting)

class TroubleshootingList(SphinxDirective):
    """
    A list of all troubleshooting entries.
    """

    has_content = False
    required_arguments = 0
    optional_arguments = 0
    final_argument_whitespace = False
    option_spec: OptionSpec = {}

    def run(self) -> List[Node]:
        # Simply insert an empty troubleshootinglist node which will be replaced later
        # when process_troubleshooting_nodes is called
        return [troubleshootinglist('')]


class TroubleshootingListProcessor:
    def __init__(self, app: Sphinx, doctree: nodes.document, docname: str) -> None:
        self.builder = app.builder
        self.config = app.config
        self.env = app.env
        self.domain = cast(TroubleshootingDomain, app.env.get_domain('troubleshooting'))
        self.document = new_document('')

        self.process(doctree, docname)

    def process(self, doctree: nodes.document, docname: str) -> None:
        troubleshootings: List[troubleshooting_node] = sum(self.domain.troubleshootings.values(), [])
        for node in list(doctree.traverse(troubleshootinglist)):
            if node.get('ids'):
                content: List[Element] = [nodes.target()]
            else:
                content = []

            for troubleshooting in troubleshootings:
                # Create a copy of the troubleshooting node
                new_troubleshooting = troubleshooting.deepcopy()
                new_troubleshooting['ids'].clear()

                self.resolve_reference(new_troubleshooting, docname)
                content.append(new_troubleshooting)

                troubleshooting_ref = self.create_troubleshooting_reference(troubleshooting, docname)
                content.append(troubleshooting_ref)

            node.replace_self(content)

    def create_troubleshooting_reference(self, troubleshooting: troubleshooting_node, docname: str) -> nodes.paragraph:
        if self.config.troubleshooting_link_only:
            description = _('<<original entry>>')
        else:
            description = (_('(The <<original entry>> is located in %s, line %d.)') %
                           (troubleshooting.source, troubleshooting.line))

        prefix = description[:description.find('<<')]
        suffix = description[description.find('>>') + 2:] # this is a great trick

        para = nodes.paragraph(classes=['troubleshooting-source'])
        para += nodes.Text(prefix, prefix)

        # Create a reference
        linktext = nodes.emphasis(_('original entry'), _('original entry'))
        reference = nodes.reference('', '', linktext, internal=True)
        try:
            reference['refuri'] = self.builder.get_relative_uri(docname, troubleshooting['docname'])
            reference['refuri'] += '#' + troubleshooting['ids'][0]
        except NoUri:
            # ignore if no URI can be determined, e.g. for LaTeX output
            pass

        para += reference
        para += nodes.Text(suffix, suffix)

        return para

    def resolve_reference(self, troubleshooting: troubleshooting_node, docname: str) -> None:
        """Resolve references in the troubleshooting content."""
        for node in troubleshooting.traverse(addnodes.pending_xref):
            if 'refdoc' in node:
                node['refdoc'] = docname

        # Note: To resolve references, it is needed to wrap it with document node
        self.document += troubleshooting
        self.env.resolve_references(self.document, docname, self.builder)
        self.document.remove(troubleshooting)


def visit_troubleshooting_node(self: HTMLTranslator, node: troubleshooting_node) -> None:
    self.visit_admonition(node)


def depart_troubleshooting_node(self: HTMLTranslator, node: troubleshooting_node) -> None:
    self.depart_admonition(node)


def setup(app: Sphinx) -> Dict[str, Any]:
    app.add_config_value('troubleshooting_include_troubleshootings', False, 'html')
    app.add_config_value('troubleshooting_link_only', False, 'html')
    app.add_config_value('troubleshooting_emit_warnings', False, 'html')

    app.add_node(troubleshootinglist,
                 html=(visit_troubleshooting_node, depart_troubleshooting_node))
    app.add_node(troubleshooting_node,
                 html=(visit_troubleshooting_node, depart_troubleshooting_node))

    app.add_directive('troubleshooting', TroubleshootingDirective)
    app.add_directive('troubleshootinglist', TroubleshootingList)
    app.add_domain(TroubleshootingDomain)
    app.connect('doctree-resolved', TroubleshootingListProcessor)
    return {
        'version': sphinx.__display_version__,
        'env_version': 2,
        'parallel_read_safe': True
    }

