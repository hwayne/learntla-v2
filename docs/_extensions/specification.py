from pathlib import Path
from typing import Any, List, Dict
# from re import sub
# from sphinx.config import Config
from sphinx.application import Sphinx
from docutils import nodes
from docutils.nodes import Node
from docutils.parsers.rst import directives # type: ignore
from sphinx.directives.code import LiteralInclude


class SpecificationDirective(LiteralInclude):
    """A QoL handler for embedding tla+ specifications.
        * Only requires the filename, not the full path
        * Automatically includes download option
        * TODO: Allows placing a state-space caption by default"
        * TODO: Allow for marking a spec as "is broken"
    """
    option_spec = LiteralInclude.option_spec | {"hide-header": directives.flag, "ss": directives.unchanged_required, "fails": directives.flag}
    def run(self) -> List[Node]:
        spec_dir = Path(self.env.srcdir) / "specs" 
        path = spec_dir / self.arguments[0]
        self.arguments[0] = path.as_posix()
        if not self.options.get('caption'):
            dl_link = f":download:`spec <{self.arguments[0]}>`"
            if ss := self.options.get('ss'):
                dl_link = f":ss:`{ss}` {dl_link}"
            elif 'fails' in self.options:
                dl_link = f"(fails) {dl_link}"
            self.options['caption'] = dl_link


        if not self.options.get('language'):
            self.options['language'] = 'tla'
        if diff := self.options.get('diff'):
            self.options['language'] = 'diff'
            self.options['diff'] = str(spec_dir / diff)
        
        out = super().run()

        if self.options.get('diff'):
            # Remove the unsightly diff prefix
            # We use the two @@ markers as waypoints, which look like tla+ symbols

            # TODO make this all a function
            # TODO this should also remove inline @@, so using a regex
            new_body = out[0][1][0].split(r'@@', maxsplit=2)[-1]
            #new_body = sub(r'\n@@[ 0-9+,-]*@@', r'\n\n\\* ... \n', new_body)


            #  ↓ Might not be needed
            _, filename = self.env.relfn2path(self.arguments[0])
            new_literal = nodes.literal_block(new_body, new_body, source=filename)
            new_literal.attributes = out[0][1].attributes
            

            out[0][1] = new_literal
        return out

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
