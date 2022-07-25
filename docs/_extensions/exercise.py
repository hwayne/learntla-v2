"""
I copied all of this from sphinx_exercise so I could make a better question and solution linker

https://www.sphinx-doc.org/en/master/development/tutorials/recipe.html
https://github.com/sphinx-doc/sphinx/blob/4.x/sphinx/ext/todo.py
https://www.sphinx-doc.org/en/master/development/tutorials/recipe.html
NOTE: Doesn't yet work for LaTeX builder

NOTE: currently errors a solution corresponds to an exercise that doesn't have a title
"""

### INCLUDES {{{
from docutils import nodes
from docutils.nodes import Node
from docutils.parsers.rst import directives
from docutils.parsers.rst.directives.admonitions import BaseAdmonition

from typing import Any, List, Dict, Set, Union, cast, Tuple
from sphinx.config import Config
from sphinx.application import Sphinx
from sphinx.environment import BuildEnvironment
from sphinx.domains.std import StandardDomain
# from sphinx.domains import Domain
from sphinx.util import logging
from sphinx.roles import XRefRole
from sphinx.util.docutils import SphinxDirective
from sphinx.directives.code import CodeBlock
from sphinx.locale import _, __

logger = logging.getLogger(__name__)
### END INCLUDES }}}


### LOCAL NODES {{{

# This is gonna be problematic if I ever want to make this into a PDF. YAGNI!!!
class dropdown_node(nodes.Element):
    ...

class exercise_node(nodes.Admonition, nodes.Element):
    pass

class part_node(nodes.Admonition, nodes.Element):
    pass


### END LOCAL NODES }}}

class ExerciseDomain(StandardDomain):
    name = 'exercise'
    label = 'ex'

    roles = {
        'ref': XRefRole()
    }

    initial_data = {
            'ex': {}
    }

    @property
    def ex(self) -> Dict[str, List[exercise_node]]:
        return self.data['ex']
        #return self.data.setdefault('ex', {})

    def clear_doc(self, docname: str) -> None:
        self.ex.pop(docname, None)

    def merge_domaindata(self, docnames: List[str], otherdata: dict) -> None:
        for docname in docnames:
            self.ex[docname] = otherdata['ex'][docname]

    def process_doc(self, env: BuildEnvironment, docname: str,
                    document: nodes.document) -> None:
        ex = self.ex.setdefault(docname, [])
        for e in document.findall(exercise_node):
            # Should also handle solution nodes
            self.process_exercise(e)
            ex.append(e)

    def process_exercise(self, exercise: exercise_node):
        ...

    def process_solution(self, sol):
        ...

### DIRECTIVES {{{

class exercise_embed(nodes.General, nodes.Element):
    pass

class ExerciseDirective(BaseAdmonition, SphinxDirective):
    """ A custom exercise directive """

    node_class = exercise_node
    has_content = True
    required_arguments = 0
    optional_arguments = 1
    final_argument_whitespace = True
    option_spec = {
        "name": directives.unchanged_required,
        "class": directives.class_option,
        "hidden": directives.flag,
        # difficulty
    }

    def run(self) -> List[Node]:
        if not self.options.get('class'):
            self.options['class'] = ['exercise']

        if n := self.options.get('name'):
            self.options['name'] = f"ex-{n}"

        (ex, ) = super().run()

        if isinstance(ex, nodes.system_message):
            return [ex]


        title = _('Exercise')
        if self.arguments:
            title = _(f"{title}: {self.arguments[0]}")
        ex.insert(0, nodes.title(text=title))
        ex['docname'] = self.env.docname
        self.add_name(ex)
        self.set_source_info(ex)
        # self.state.document.note_explicit_target(ex)
        return [ex] 

class HiddenContentDirective(BaseAdmonition, SphinxDirective):
    """ A directive for controlling all kinds of "hidable" content, namely solutions, hints, and tests. """

    node_class = dropdown_node
    has_content = True
    required_arguments = 0
    optional_arguments = 0
    final_argument_whitespace = False
    option_spec = {
        "name": directives.unchanged_required,
        "class": directives.class_option,
        "hidden": directives.flag,
        "tla": directives.flag # not used, yet.
    }

    css = "dropdown"
    label = "Dropdown"

    def run(self) -> List[Node]:
        (node,) = super().run()
 #       (node,) = CodeBlock(**self).run()

        if isinstance(node, nodes.system_message):
            return [node]

        if not self.options.get('class'):
            node['class'] = f"hiddencontent {self.css_class}"
        node['show_label'] = self.show_label
        return [node]

    @property
    def css_class(self):
        return self.__class__.css

    @property
    def show_label(self):
        return self.__class__.label

class HintDirective(HiddenContentDirective):
    css = "hint"
    label = "Hint"

class SolutionDirective(HiddenContentDirective):
    css = "solution"
    label = "Solution"

# class SolutionDirective(BaseAdmonition, SphinxDirective):
#     """ A custom solution directive """
# 
#     node_class = solution_node
#     has_content = True
#     required_arguments = 0
#     optional_arguments = 0
#     final_argument_whitespace = False
#     option_spec = {
#         "name": directives.unchanged_required,
#         "class": directives.class_option,
#         "hidden": directives.flag,
#     }
# 
#     def run(self) -> List[Node]:
#         (sol,) = super().run()
# 
#         if isinstance(sol, nodes.system_message):
#             return [sol]
# 
#         return [sol]
        # Register parent

### END DIRECTIVES }}}


### APP {{{


def visit_exercise_node(self, node):
    self.visit_admonition(node)

def depart_exercise_node(self, node):
    self.depart_admonition(node)

def visit_solution_node(self, node):
    self.body.append(f"""<div><details class="{node['class']}">
      <summary>
        {node['show_label']}
      </summary>""")
    self.visit_paragraph(node)

def depart_solution_node(self, node):
    self.depart_paragraph(node)
    self.body.append("</details></div>")

def setup(app: Sphinx) -> Dict[str, Any]:

    app.add_node(exercise_node,
                 html=(visit_exercise_node, depart_exercise_node),
            )

    app.add_node(dropdown_node,
                 html=(visit_solution_node, depart_solution_node),
            )
    
    app.add_directive('exercise', ExerciseDirective)
    app.add_directive('solution', SolutionDirective)
    app.add_directive('hint', HintDirective)
    app.add_domain(ExerciseDomain)

    # app.connect("doctree-resolved", DoctreeResolve)

    return {
        "version": "builtin",
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }


def get_title(self):
    return self[0].astext()

### END APP }}}


