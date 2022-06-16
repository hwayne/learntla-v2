
from sphinx.application import Sphinx 
from sphinx.util.docutils import SphinxRole
from pathlib import Path
from typing import Any
from docutils.nodes import Node
from docutils import nodes
from sphinx import roles
import yaml
import sys

# https://stackoverflow.com/questions/20553551/how-do-i-get-pylint-to-recognize-numpy-members
class StateSpaceRole(SphinxRole):
    """Used to dynamically add 'error checks' to learntla specs.
    Since TLA+ doesn't provide a lot of feedback, the best way for users to check
    if they have the correct spec written is by comparing the number of states and distinct states.
    We store this information in modelchecks.yml. This role automatically inserts
    (n states / m distinct) for a given model check.

    """
    def run(self) -> tuple[list[Node], list[Any]]:
        if not hasattr(self.env, 'state_spaces'):
            p = Path(self.env.srcdir) / "./data.yml"
            self.env.state_spaces = yaml.load(p.read_text(), Loader=yaml.Loader)["state_spaces"]

        try:
            data = self.env.state_spaces[self.text]

        # Error handling if the key is not found
        except KeyError:
            msg = self.inliner.reporter.error(
                f"role was not able to find a state space with name {self.text}", line=self.lineno)
            #prb = (self.rawtext, self.rawtext, msg)
            prb = self.inliner.problematic(self.rawtext, self.rawtext, msg)
            return [prb], [msg]

        body = f"{data['states']:n} states / {data['distinct']:n} distinct"

        node = nodes.inline(self.rawtext, body) 


        self.env.note_dependency(__file__) # Rebuild everything if I change this role

        return [node], []
        # Add build information that can be read by neovim pumbl

def setup(app: Sphinx):

    app.add_role('ss', StateSpaceRole())
    return {
        "version": 0.1,
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }

