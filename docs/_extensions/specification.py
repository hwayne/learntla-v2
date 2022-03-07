from pathlib import Path
from typing import Any, List, Dict
# from sphinx.config import Config
from sphinx.application import Sphinx
from docutils import nodes
from docutils.nodes import Node
from sphinx.util.docutils import SphinxDirective
from docutils.parsers.rst import directives # type: ignore
from sphinx.directives.code import LiteralInclude


class SpecificationDirective(LiteralInclude):
    """A QoL handler for embedding tla+ specifications.
        * Only requires the filename, not the full path
        * Automatically includes download option
        * Has option to hide header and footer
    """
    option_spec = LiteralInclude.option_spec | {"hide-header": directives.flag}
    def run(self) -> List[Node]:
        spec_dir = Path(self.env.srcdir) / "specs" 
        path = spec_dir / self.arguments[0]
        self.arguments[0] = path.as_posix()
        if not self.options.get('caption'):
            dl_link = f":download:`spec <{self.arguments[0]}>`"
            self.options['caption'] = dl_link

        if not self.options.get('language'):
            self.options['language'] = 'tla'
        if diff := self.options.get('diff'):
            self.options['diff'] = str(spec_dir / diff)
        #out = super().run()
        #breakpoint()
        #out[0][1][0].text
        return super().run()

class TroubleshootingDirective(nodes.Admonition):
    ...

def setup(app: Sphinx) -> Dict[str, Any]:


    app.add_directive("spec", SpecificationDirective)

    # TODO move to their own thing
    #app.add_directive("troubleshooting", TroubleshootingDirective)

    return {
        "version": "builtin",
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }
