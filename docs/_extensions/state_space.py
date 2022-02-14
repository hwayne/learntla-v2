from sphinx.application import Sphinx
from sphinx.util.docutils import SphinxRole
from pathlib import Path
from typing import Any
from docutils.nodes import Node, TextElement
from docutils import nodes
import yaml


# make this use the proper class, so we can load the environment once
class StateSpaceRole(SphinxRole):
    """Used to dynamically add 'error checks' to learntla specs.
    Since TLA+ doesn't provide a lot of feedback, the best way for users to check
    if they have the correct spec written is by comparing the number of states and distinct states.
    We store this information in modelchecks.yml. This role automatically inserts
    (n states / m distinct) for a given model check.

    TODO: commas
    """
    ...

def state_space_role(name, rawtext, text, lineno, inliner,
            options=None, content=None) -> tuple[list[Node], list[Any]]:

    # Make this use the sphinx-path
    p = Path(r"./data.yml")
    try:
        data = yaml.load(p.read_text())["state_spaces"][text]

    # Error handling if the key is not found
    except KeyError:
        msg = inliner.reporter.error(
            f"role was not able to find a state space with name {text}", line=lineno)
        prb = inliner.problematic(rawtext, rawtext, msg)
        return [prb], [msg]

    body = f"({data['states']} states / {data['distinct']} distinct)"

    node = nodes.inline(rawtext, body)

    return [node], []

def setup(app: Sphinx):

    app.add_role('ss', state_space_role)
    return {
        "version": 0.1,
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }

