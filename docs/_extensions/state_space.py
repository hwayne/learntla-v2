from sphinx.application import Sphinx
from pathlib import Path
from typing import Any
from docutils.nodes import Node, TextElement
from docutils import nodes
import yaml


# make this use the proper class, so we can load the environment once
def state_space_role(name, rawtext, text, lineno, inliner,
            options=None, content=None) -> tuple[list[Node], list[Any]]:

    # Make this use the sphinx-path
    p = Path(r"./data.yml")
    data = yaml.load(p.read_text())["spaces"][text]

    # Error handling if the key is not found
    ...

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

