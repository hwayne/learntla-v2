import xml.etree.ElementTree as ET
from xml.etree.ElementTree import Element
from copy import deepcopy
from argparse import ArgumentParser
from dataclasses import dataclass
from string import Template
from pathlib import Path

"""This is used to process specs into a form that we can use, and also update the data file."""
parser = ArgumentParser()
parser.add_argument("file", help="xml file to convert")
parser.add_argument("--spec", required=False, help="spec in the file to convert. Leave out if all")
parser.add_argument("--version", required=False, help="which version of the spec. Should only be used if --spec is also used. Leave out if all. TODO find how argparse works for better documentation of flag limitations")
# TODO add flag to write them instead of dryrun parser.add_argument("--version", required=False, help="which version of the spec. Should only be used if --spec is also used. Leave out if all. TODO find how argparse works for better documentation of flag limitations")
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
                b = 20 # Like I'll ever have more
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

def create_spec_version(spec_root: Element, version: int) -> Spec:
    new_version = deepcopy(spec_root)

    for switch in new_version.findall('.//s'):
        if version not in get_on(switch):
            for child in switch.iter():
                # includes switch
                child.text = "" # make this also eliminate child element tex 
    return Spec(
        name=new_version.attrib["name"],
        version=version,
        text=tree_to_text(new_version)
        )

def create_all_spec_versions(spec_root: Element) -> list[Spec]:
    out = []
    num_versions = int(spec_root.attrib["num"])
    for i in range(1, num_versions+1):
        out.append(create_spec_version(spec_root, i))
    return out
    

if __name__ == "__main__":
    tree = ET.parse(args.file)
    folder = tree.getroot().attrib["folder"]
    out: list[Spec] = []
    if args.spec:
        spec_root = tree.find(f"spec[@name='{args.spec}']")
        assert spec_root is not None # did we get the name wrong
        if args.version:
            out = [create_spec_version(spec_root, int(args.version))]
        else:
            out = create_all_spec_versions(spec_root)
    else:
        specs = tree.findall(f"spec")
        for spec_root in specs:
            out += create_all_spec_versions(spec_root)

    for spec in out:
        out_path = Path(folder) / f"{spec.filename()}.tla"
        to_write = str(spec)
        if out_path.exists():
            parts = out_path.read_text().split("!!!")
            parts[-1] = to_write
            to_write = "!!!".join(parts)
        
        out_path.write_text(to_write)
        

        
        
