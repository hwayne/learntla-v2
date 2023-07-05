# Learntla V2

A guide to learning the TLA+ specification language. Going to be a gigantic mess right now, will be a while before the dust settles. 


## Usage

### Installation

Requires Python 3.10.

```
git clone https://github.com/hwayne/learntla-v2.git
python -m venv learntla-v2
# Activate the venv yo
python -m pip install -r requirements.txt
```

### Building

```
# with todos
sphinx-build docs/ docs/_build/html/

# without todos
sphinx-build -D todo_include_todos=0 docs/ docs/_build/html/

# check links for issues
sphinx-build -b linkcheck docs/ docs/_build/
```

### Working with Specs

See the [raw-specs readme](/raw-specs/README.md) for explanation of what these are for.

To expand an xml template:

```
# dryrun
python expand_template.py --dryrun file.xml

# actually write files
python expand_template.py file.xml
```

To process a spec, write

```
# one file
python process_spec.py file.tla

# every file in a folder
ConvertFolder.ps1 folder
```

### Watcher.ps1

Builds the site whenever an rst file changes. Can be ignored, unnecessary for development.

Requires 

```
Install-Module -Name FSWatcherEngineEvent
```
