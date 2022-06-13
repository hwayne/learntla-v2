from pathlib import Path
from typing import Any, List, Dict
# from re import sub
# from sphinx.config import Config
from sphinx.application import Sphinx
from docutils import nodes
from docutils.nodes import Node
from docutils.parsers.rst import directives # type: ignore
from sphinx.directives.code import LiteralInclude
from sphinx.writers.html import HTMLTranslator
from state_space import StateSpaceRole


class spec_caption_node(nodes.caption):
    ...

def visit_spec_caption_node(self: HTMLTranslator, node: spec_caption_node) -> None:
    self.body.append(self.starttag(
            node, 'div', CLASS=('spec-caption')))


def depart_spec_caption_node(self: HTMLTranslator, node: spec_caption_node) -> None:
    self.body.append('</div>\n')


class SpecificationDirective(LiteralInclude):
    """A QoL handler for embedding tla+ specifications.
        * Only requires the filename, not the full path
        * Automatically includes download option
        * Bottom caption for if model passes or fails
        * Cleanly handles diffs
    """
    option_spec = LiteralInclude.option_spec | {"hide-header": directives.flag, "ss": directives.unchanged_required, "fails": directives.flag}

    def run(self) -> List[Node]:
        spec_dir = Path(self.env.srcdir) / "specs" 
        path = spec_dir / self.arguments[0]
        self.arguments[0] = path.as_posix()


        if not self.options.get('language'):
            self.options['language'] = 'tla'
        if diff := self.options.get('diff'):
            self.options['language'] = 'diff'
            self.options['diff'] = str(spec_dir / diff)
        
        self.options['caption'] = self.get_caption()

        out = super().run()

        if self.options.get('diff'):
            # Remove the unsightly diff prefix
            # We use the two @@ markers as waypoints, which look like tla+ symbols

            # TODO make this all a function
            # TODO this should also remove inline @@, so using a regex
            new_body = out[0][1][0].split(r'@@', maxsplit=2)[-1]
            #new_body = sub(r'\n@@[ 0-9+,-]*@@', r'\n\n\\* ... \n', new_body)


            new_literal = nodes.literal_block(new_body, new_body)

            new_literal.attributes = out[0][1].attributes
            out[0][1] = new_literal

        
        # move caption below block
        try:
            out[0][0], out[0][1] = out[0][1], out[0][0]
        except:
            breakpoint()
            quit()
         

        return out

    def get_caption(self):
        dl_link = f":download:`spec <{self.arguments[0]}>`"
        if ss := self.options.get('ss'):
            dl_link = f":ss:`{ss}` {dl_link}"
        elif 'fails' in self.options:
            dl_link = f"(fails) {dl_link}"
        return dl_link


def setup(app: Sphinx) -> Dict[str, Any]:
    app.add_directive("spec", SpecificationDirective)


    app.add_node(spec_caption_node, html=(visit_spec_caption_node, depart_spec_caption_node))


    return {
        "version": "builtin",
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }
