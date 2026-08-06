# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
import os
import sys
sys.path.insert(0, os.path.abspath('.'))
sys.path.append(os.path.abspath('_extensions'))

# -- Project information -----------------------------------------------------

project = 'learntla'
copyright = '2022, Hillel Wayne'
author = 'Hillel Wayne'

version = "0.2"
release = "0.2"

needs_sphinx = "4.4.0"

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    'sphinx.ext.todo',
    'sphinx.ext.githubpages',
    'sphinx.ext.graphviz',
    'piccolo_theme',
    'sphinx_copybutton',
    'exercise',
    'state_space',
    'specification',
    'troubleshooting',
]
# https://github.com/mgaitan/sphinxcontrib-mermaid/tree/master/docs
# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store', '**/advanced']

replace = {
    "core": ":doc:`Core </core/index>`",
    "topics": ":doc:`Topics </topics/index>`",
    "examples": ":doc:`Examples </examples/index>`",

}


epilog_template = lambda x, y: f".. |{x}| replace:: {y}"
rst_epilog = "\n".join([epilog_template(k,v) for k,v in replace.items()])

numfig = False
smartquote = False

# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'piccolo_theme'
html_title = "Learn TLA+"
html_short_title = "Learn TLA+"
default_role = "any"
highlight_language = "tla"
html_style = "custom.css"

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']
html_css = ["custom.css"]
todo_include_todos = True
trim_footnote_reference_space = True

# Graphviz ext
graphviz_dot_args=["-Grankdir=LR", "-Glabelloc=t", "-Nshape=rect", "-Nfontname=Fira Code",  "-Efontname=Fira Code"]
