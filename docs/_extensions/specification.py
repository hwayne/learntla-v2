from pathlib import Path
from typing import Any, List, Dict, Set, Union, cast
from sphinx.config import Config
from sphinx.application import Sphinx
from docutils import nodes
from docutils.nodes import Node
from sphinx.util.docutils import SphinxDirective
from docutils.parsers.rst import directives
from sphinx.directives.code import LiteralInclude


class SpecificationDirective(LiteralInclude):
    """A QoL handler for embedding tla+ specifications.
        * Only requires the filename, not the full path
        * Automatically includes download option
        * Has option to hide header and footer
    """
    option_spec = LiteralInclude.option_spec | {"hide-header": directives.flag}
    def run(self) -> List[Node]:

        if not self.options.get('language'):
            self.options['language'] = 'tla'
        if not self.options.get('caption'):
            self.options['caption'] = "TODO"
        path = Path(self.env.srcdir) / "specs" / self.arguments[0]
        self.arguments[0] = str(path)
        return super().run()

def setup(app: Sphinx) -> Dict[str, Any]:


    app.add_directive("spec", SpecificationDirective)

    return {
        "version": "builtin",
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }
