from pathlib import Path
from typing import Any
from argparse import ArgumentParser
from re import sub
import yaml

"""This is used to process specs into a form that we can use, and also update the data file."""
parser = ArgumentParser()
parser.add_argument("spec", help="Spec file to translate")

# Arguments to control if we're updating just the file or also the state spaces
args = parser.parse_args()

spec_path = Path(args.spec)

spec = spec_path.read_text()
parts = spec.split("!!!")

yml = yaml.load(parts[0], Loader=yaml.Loader)
out = Path("../") / "docs" / yml['target']

remove_translation = r"\\\* BEGIN TRANSLATION(.|\n)*" + r"\\\* END TRANSLATION.*\n"
cleaned_spec = sub(remove_translation, "", parts[-1]).lstrip()

rename_module = r"MODULE (\w|_)+"
cleaned_spec = sub(rename_module, f"MODULE {out.stem}", cleaned_spec)

out.write_text(cleaned_spec)

# TODO figure out the proper format to mess with configs and 

data_file = Path("../docs/data.yml") # move this
data = yaml.load(data_file.read_text(), Loader=yaml.Loader)
data["state_spaces"] |= yml["states"]
data_file.write_text(yaml.dump(data))


