import xml.etree.ElementTree as ET
from xml.etree.ElementTree import Element, ElementTree
from copy import deepcopy
from argparse import ArgumentParser
from dataclasses import dataclass
from string import Template

"""This is used to process specs into a form that we can use, and also update the data file."""
parser = ArgumentParser()
parser.add_argument("file", help="xml file to convert")
parser.add_argument("--spec", required=False, help="spec in the file to convert. Leave out if all")
parser.add_argument("--version", required=False, help="which version of the spec. Leave out if all")
# Arguments to control if we're updating just the file or also the state spaces
args = parser.parse_args()

"""Common issue is that I need to have multiple slightly different versions of the same spec, this is a helper to do that.
"""
def expand_on_attrib(on_str: str) -> set[int]:
    out = set()
    on = on_str.split(',')
    for i in on:
        if "-" in i:
            a,b = i.split("-")
            if not a:
                a = 1
            else:
                a = int(a)
            if not b:
                b = 20 # Close enough
            else:
                b = int(b)
            out |= set(range(a, b+1))
        else:
            out.add(int(i))
    return out

def get_on(s: Element) -> set[int]: 
    return expand_on_attrib(s.attrib["on"])

def tree_to_text(tree) -> str:
    return "".join(tree.itertext())

@dataclass
class Spec:
    name: str
    version: int
    text: str

    def filename(self):
        return f"{self.name}__{self.version}"

    def __str__(self):
        return Template(self.text).substitute({"name": self.filename()})

def create_spec_version(spec_tree: Element, version: int) -> Spec:
    version_tree = deepcopy(spec_tree)

    for switch in version_tree.findall('.//s'):
        if version not in get_on(switch):
            switch.text = "" # make this also eliminate child element text
    return Spec(
        name=version_tree.attrib["name"],
        version=version,
        text=tree_to_text(version_tree)
        )

def create_all_spec_versions(spec_root: Element) -> list[Spec]:
    out = []
    num_versions = int(spec_root.attrib["num"])
    for i in range(1, num_versions+1):
        out.append(create_spec_version(spec_root, i))
    return out
    

if __name__ == "__main__":
    tree = ET.parse(args.file)
    v1 = tree.find("spec[@name='duplicates']")
    S = create_all_spec_versions(v1)
    [print(s) for s in S]
