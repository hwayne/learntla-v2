"""
I copied all of this from sphinx_exercise so I could make a better question and solution linker


NOTE: Doesn't yet work for LaTeX builder

"""

### INCLUDES {{{

from pathlib import Path
from typing import Any, List, Dict, Set, Union, cast
from sphinx.config import Config
from sphinx.application import Sphinx
from sphinx.environment import BuildEnvironment
from sphinx.domains.std import StandardDomain
from sphinx.addnodes import number_reference
from docutils.nodes import Node
from docutils import nodes
from sphinx.util import logging
from sphinx.util.fileutil import copy_asset
from sphinx.util.docutils import SphinxDirective
from docutils.parsers.rst import directives

logger = logging.getLogger(__name__)
### END INCLUDES }}}


### LOCAL NODES {{{

def is_enumerable_node(node):
    return isinstance(node, enumerable_node)


def is_unenumerable_node(node):
    return isinstance(node, unenumerable_node)


def is_linked_node(node):
    return isinstance(node, linked_node)


def is_extension_node(node):
    return (
        is_enumerable_node(node) or is_unenumerable_node(node) or is_linked_node(node)
    )


class enumerable_node(nodes.Admonition, nodes.Element):
    pass


def visit_enumerable_node(self, node: Node) -> None:
    # import traceback
    # traceback.print_stack()
    # assert False
    self.visit_admonition(node)


def depart_enumerable_node(self, node: Node) -> None:
    self.depart_admonition(node)


class unenumerable_node(nodes.Admonition, nodes.Element):
    pass


def visit_unenumerable_node(self, node: Node) -> None:
    self.visit_admonition(node)


def depart_unenumerable_node(self, node: Node) -> None:
    self.depart_admonition(node)


class linked_node(nodes.Admonition, nodes.Element):
    pass


def visit_linked_node(self, node: Node) -> None:
    self.visit_admonition(node)


def depart_linked_node(self, node: Node) -> None:
    self.depart_admonition(node)

### END LOCAL NODES }}}

### DIRECTIVES {{{

class CustomDirective(SphinxDirective):
    """ A custom Sphinx directive """

    name = ""

    def run(self) -> List[Node]:
        


        if not hasattr(self.env, "exercise_list"):
            # Creating global state, by setting it on self.env
            self.env.exercise_list = {}

        # Probably for CSS classes
        classes, class_name = [self.name], self.options.get("class", "")
        if class_name:
            classes.extend(class_name)

        ### TITLE SHIT {{{
        title_text, title = "", ""
        if self.name == "exercise":
            if "nonumber" in self.options:
                title_text = f"{self.name.title()} "

            if self.arguments:
                title_text += f"({self.arguments[0]})"
                title += self.arguments[0]
        else:
            # Solution to"
            title_text = f"{self.name.title()} to "
            target_label = self.arguments[0]

        ### /TITLE SHIT }}}

        textnodes, _ = self.state.inline_text(title_text, self.lineno)

        section = nodes.section(ids=[f"{self.name}-content"]) # ^v<???
        self.state.nested_parse(self.content, self.content_offset, section)

        label = self.get_label()

        # I think we need to add this now, and then actually replace it in the  doctree resolve
        if self.name == "exercise":
            # I think I need an inline here for replacement?
            ref = nodes.reference("", "", sol_link=True)
            ref["refid"] = f"{label}-sol"
            p = nodes.paragraph("", "")
            p += ref
            section += p

        node = self.base_node_type()

        node += nodes.title(title_text, "", *textnodes)
        node += section
        #breakpoint()
        #logger.warning(node, color="blue")# }}}
        # This is where we'd add the reference for exercises to the solutions



        # Duplicate label warning
        if label in self.env.exercise_list.keys(): # Is "" ever in keys?
            self.warn_about_duplicates(label)
            return []

        self.options["name"] = label

        # Set node attributes
        node["classes"].extend(classes)
        node["ids"].append(label)
        node["label"] = label
        node["docname"] = self.env.docname
        node["hidden"] = True if "hidden" in self.options else False
        node.document = self.state.document
        # For the exercise, what I'd do is append to the document end, the reference to the solution?

        if self.name == "solution":
            node["target_label"] = target_label

        self.add_name(node) # ???

        self.env.exercise_list[label] = {
            "type": self.name,
            "docname": self.env.docname,
            "node": node,
            "title": title,
            "hidden": node.get("hidden", bool),
        }

        # Can't go earlier because we need to update exercise list
        if node.get("hidden", bool):
            return []

        return [node]


    def warn_about_duplicates(self, label): # {{{
        docpath = self.env.doc2path(self.env.docname)
        path = docpath[: docpath.rfind(".")] # Sphinx's local relative path
        other_path = self.env.doc2path(self.env.exercise_list[label]["docname"])
        msg = f"duplicate label: {label}; other instance in {other_path}"
        logger.warning(msg, location=path, color="red")# }}}

    def get_label(self):
        # As it stands, this will horrible break if called multiple times for the same directive, due to the new_serialno()
        label = self.options.get("label", "")
        if label:
            self.options["noindex"] = False
        else:
            self.options["noindex"] = True
            serial_no = self.env.new_serialno() #incrementing id?
            label = f"{self.env.docname}-{self.name}-{serial_no}" # Autogen IFF not existing label
        return label

class ExerciseDirective(CustomDirective):
    """ A custom exercise directive """

    name = "exercise"
    has_content = True
    required_arguments = 0
    optional_arguments = 1
    final_argument_whitespace = True
    option_spec = {
        "label": directives.unchanged_required, # probably a sphinx thing, might be `str or None`
        "class": directives.class_option,
        "nonumber": directives.flag,
        "hidden": directives.flag,
    }

    def base_node_type(self):
        if "nonumber" in self.options:
            return unenumerable_node()
        return enumerable_node()


class SolutionDirective(CustomDirective):
    """ A custom solution directive """

    name = "solution"
    has_content = True
    required_arguments = 1
    optional_arguments = 0
    final_argument_whitespace = False
    option_spec = {
        "label": directives.unchanged_required,
        "class": directives.class_option,
        "hidden": directives.flag,
    }

    def run(self) -> List[Node]:
        # HI-LARIOUS breaking of LSP
        if self.env.app.config.hide_solutions:
            return []
        return super().run()

    def base_node_type(self):
        return linked_node()

    def get_label(self):
        # if it's a solution, then we set node["label"] to node["target_label"] + "-sol"
        target_label = self.arguments[0]
        return f"{target_label}-sol"

### END DIRECTIVES }}}


### APP {{{

def purge_exercises(app: Sphinx, env: BuildEnvironment, docname: str) -> None:
    if not hasattr(env, "exercise_list"):
        return

    env = cast(Any, env)
# Override env.exercise_list
    env.exercise_list = {
        exercise: env.exercise_list[exercise]
        for exercise in env.exercise_list.keys()
        if env.exercise_list[exercise]["docname"] != docname
    }


def merge_exercises(
    app: Sphinx, env: BuildEnvironment, docnames: Set[str], other: BuildEnvironment
) -> None:
    if not hasattr(env, "exercise_list"):
        setattr(env, "exercise_list", {})

    # Merge env stored data
    if hasattr(other, "exercise_list"):
        env.exercise_list = {**env.exercise_list, **other.exercise_list}


def init_numfig(app: Sphinx, config: Config) -> None:
    """Initialize exercise numfig format."""

    config["numfig"] = True
    numfig_format = {
        "exercise": "Exercise %s",
    }
    numfig_format.update(config.numfig_format)
    config.numfig_format = numfig_format


def copy_asset_files(app: Sphinx, exc: Union[bool, Exception]):
    static_path = Path(__file__).parent.joinpath("_static", "exercise.css").absolute()
    asset_files = [str(static_path)]

    if exc is None:
        for path in asset_files:
            copy_asset(path, str(Path(app.outdir).joinpath("_static").absolute()))


def doctree_read(app: Sphinx, document: Node) -> None:
    domain = cast(StandardDomain, app.env.get_domain("std"))

    # Traverse extension nodes
    for node in document.traverse():
        docname, labelid, sectname = "", "", ""

        if is_extension_node(node):
            name = node.get("names", [])[0]
            labelid = document.nameids[name]
            docname = app.env.docname

            # If solution node
            if is_linked_node(node):
                sectname = "Solution to "
            else:
                # If other node, simply add :math: to title
                # to allow for easy parsing in ref_node
                for item in node[0]:
                    if isinstance(item, nodes.math):
                        sectname += f":math:`{item.astext()}` "
                        continue
                    sectname += f"{item.astext()} "

                # Lastly, remove parans from title
                _r, _l = sectname.rfind(")"), sectname.find("(") + 1
                sectname = sectname[_l:_r].strip()

            # Now update domain.anonlabels and domain.labels
            # to include the newly updated sectname
            domain.anonlabels[name] = docname, labelid
            domain.labels[name] = docname, labelid, sectname


class DoctreeResolve:
    def __init__(self, app: Sphinx, doctree: nodes.document, docname: str) -> None:
        self.builder = app.builder
        self.config = app.config
        self.env = app.env
        self.docname = docname
        self.domain = cast(StandardDomain, app.env.get_domain("std"))
        self.process(doctree, docname)

    def _is_node_type(self, node: Node, node_type: Any) -> bool:
        return node.__class__ == node_type

    def _update_linked_node_title(self, node):
        target_labelid = node.get("target_label", "")

        try:
            target_attr = self.env.exercise_list[target_labelid]
        except Exception:
            # target_labelid not found
            docpath = self.env.doc2path(self.builder.current_docname)
            path = docpath[: docpath.rfind(".")]
            msg = f"undefined label: {target_labelid}"
            logger.warning(msg, location=path, color="red")
            node[0].insert(1, nodes.Text("Exercise", "Exercise"))
            self.env.exercise_list[node.get("label", "")]["node"] = node
            return

        target_node = target_attr.get("node", Node)

        # If linked node references an enumerable node
        # then replace title to "Solution to Exercise #"

        if is_enumerable_node(target_node):
            target_docname = target_attr.get("docname", "")
            target_type = self.domain.get_enumerable_node_type(target_node)
            target_number = self.domain.get_fignumber(
                self.env, self.builder, target_type, target_docname, target_node
            )
            target_num = ".".join(map(str, target_number))
            text = f"{target_type.title()} {target_num}"
            node[0].insert(1, nodes.Text(text, text))
        else:
            # If linked node references an unenumerable node
            # If title exists
            target_ttl = target_attr.get("title", "")
            if target_ttl:

                # Remove parans
                title = target_node[0]

                if len(title) == 1 and isinstance(title[0], nodes.Text):
                    _ = (
                        title[0]
                        .replace("Exercise", "")
                        .replace("(", "")
                        .replace(")", "")
                        .strip()
                    )
                    node[0].insert(1, nodes.Text(_, _))
                else:
                    new_title = self._update_title(title)
                    new_title.insert(0, node[0][0])
                    node.replace(node[0], new_title)
            else:
                text = "Exercise"
                node[0].insert(1, nodes.Text(text, text))

        # Create a reference
        newnode = nodes.title()
        refnode = nodes.reference()
        refnode["refdocname"] = target_attr.get("docname", "")
        refnode["refuri"] = self.builder.get_relative_uri(
            self.docname, target_attr.get("docname", "")
        )
        refnode["refuri"] += "#" + target_labelid
        inline = nodes.inline()
        title_node = node[0][0]
        for item in node[0][1:]:
            inline.append(item)
        refnode += inline
        newnode += refnode
        newnode.insert(0, title_node)
        node[0].replace_self(newnode)

        # update node
        self.env.exercise_list[node.get("label", "")]["node"] = node

    def _update_title(self, title):
        inline = nodes.inline()

        if len(title) == 1 and isinstance(title[0], nodes.Text):
            _ = title[0][0].replace("(", "").replace(")", "")
            inline += nodes.Text(_, _)
        else:
            for ii in range(len(title)):
                item = title[ii]

                if ii == 0 and isinstance(item, nodes.Text):
                    _ = item.replace("Exercise", "").replace("(", "").lstrip()
                    title.replace(title[ii], nodes.Text(_, _))
                elif ii == len(title) - 1 and isinstance(item, nodes.Text):
                    _ = item.replace(")", "").rstrip()
                    if _:
                        title.replace(title[ii], nodes.Text(_, _))
                    else:
                        continue
                inline += title[ii]

        return inline

    def _has_math_child(self, node):
        for item in node:
            if isinstance(item, nodes.math):
                return True
        return False

    # Might be important?
    def _update_ref(self, node: Node, labelid: str) -> None:
        source_attr = self.env.exercise_list[labelid]
        source_node = source_attr.get("node", Node)

        if is_linked_node(source_node):
            default_title = "Solution to "
            target_labelid = source_node.get("target_label", "")
            target_attr = self.env.exercise_list[target_labelid]
            target_node = target_attr.get("node", Node)

            if is_enumerable_node(target_node) and node.astext() == default_title:
                node[0].extend(source_node[0][1][0])
                return

            if is_unenumerable_node(target_node) and node.astext() == default_title:
                if target_attr.get("title"):
                    if self._has_math_child(target_node[0]):
                        title = self._update_title(target_node[0])
                        title.insert(0, nodes.Text(default_title, default_title))
                        node.replace(node[0], title)
                    else:
                        text = target_attr.get("title", "")
                        node[0].insert(len(node[0]), nodes.Text(text, text))
                else:
                    node[0].insert(len(node[0]), nodes.Text("Exercise", "Exercise"))
        else:
            # If no node.astext() simply add "Exercise"
            if is_enumerable_node(source_node) and not node.astext():
                text = nodes.Text("Exercise", "Exercise")
                node[0].insert(0, text)
                return



            if ":math:" in node.astext():
                title = self._update_title(source_node[0])
                node.replace(node[0], title)

    def _update_numref(self, node, labelid):
        source_attr = self.env.exercise_list[labelid]
        source_node = source_attr.get("node", Node)
        node_title = node.get("title", "")

        if "{name}" in node_title and self._has_math_child(source_node[0]):
            newtitle = nodes.inline()
            for item in node_title.split():
                if item == "{name}":
                    # use extend instead?
                    for _ in self._update_title(source_node[0]):
                        newtitle += _
                elif item == "{number}":
                    source_docname = source_attr.get("docname", "")
                    source_type = self.domain.get_enumerable_node_type(source_node)
                    source_number = self.domain.get_fignumber(
                        self.env, self.builder, source_type, source_docname, source_node
                    )
                    source_num = ".".join(map(str, source_number))
                    newtitle += nodes.Text(source_num, source_num)
                else:
                    newtitle += nodes.Text(item, item)
                newtitle += nodes.Text(" ", " ")

            if newtitle[len(newtitle) - 1].astext() == " ":
                newtitle.pop()
            node.replace(node[0], newtitle)

    def _get_refuri(self, node):
        id_ = ""
        if node.get("refuri", ""):
            id_ = node.get("refuri", "")

        if node.get("refid", ""):
            id_ = node.get("refid", "")

        return id_.split("#")[-1]

    def _update_exercise_solution_link(self, node, labelid):
        target_attr = self.env.exercise_list[labelid]
        text = nodes.inline("Solution", "Solution")
        node["refdocname"] = target_attr.get("docname", "")
        node["refuri"] = self.builder.get_relative_uri(
            self.docname, target_attr.get("docname", "")
        )
        node["refuri"] += "#" + labelid
        node += text
        #logger.warning(node, color="green")

    def process(self, doctree: nodes.document, docname: str) -> None:

        # # If linked node, update title
        for node in doctree.traverse(linked_node):
            self._update_linked_node_title(node)

        # Traverse ref and numref nodes
        for node in doctree.traverse():

            if not hasattr(self.env, "exercise_list"):
                continue

            # If node type is ref
            if isinstance(node, nodes.reference):
                labelid = self._get_refuri(node)

                # If extension directive referenced
                if labelid in self.env.exercise_list:
                    # Update displayed href text
                    self._update_ref(node, labelid)

                    ### HACKY MCHACKFACE
                    if node.hasattr("sol_link"):
                        self._update_exercise_solution_link(node, labelid)

            # If node type is numref
            if isinstance(node, number_reference):
                labelid = self._get_refuri(node)

                # If extension directive referenced
                if labelid in self.env.exercise_list:

                    # Update displayed href text
                    self._update_numref(node, labelid)


def setup(app: Sphinx) -> Dict[str, Any]:

    app.add_config_value("hide_solutions", False, "env")

    app.add_css_file("exercise.css")
    app.connect("build-finished", copy_asset_files)
    app.connect("config-inited", init_numfig)
    app.connect("env-purge-doc", purge_exercises)
    app.connect("env-merge-info", merge_exercises)
    app.connect("doctree-read", doctree_read)

    app.add_enumerable_node(
        enumerable_node,
        "exercise",
        get_title,
        html=(visit_enumerable_node, depart_enumerable_node),
        latex=(visit_enumerable_node, depart_enumerable_node),
    )

    app.add_node(
        unenumerable_node,
        html=(visit_unenumerable_node, depart_unenumerable_node),
        latex=(visit_unenumerable_node, depart_unenumerable_node),
    )

    app.add_node(
        linked_node,
        html=(visit_linked_node, depart_linked_node),
        latex=(visit_linked_node, depart_linked_node),
    )

    app.add_directive("exercise", ExerciseDirective)
    app.add_directive("solution", SolutionDirective)

    app.connect("doctree-resolved", DoctreeResolve)

    return {
        "version": "builtin",
        "parallel_read_safe": True,
        "parallel_write_safe": True,
    }


def get_title(self):
    return self[0].astext()

### END APP }}}

