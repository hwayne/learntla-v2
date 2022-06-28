# Learntla V2

A complete ground-up rewrite of the original [learntla](https://old.learntla.com). Going to be a gigantic mess right now, will be a while before the dust. Assume that everything in it rn is 1) wrong, 2) broken, and 3) wrong and broken.

TODO write a roadmap and stuff

## Setting up

### Windows

Install Python from https://www.python.org/downloads/

```
git clone https://github.com/hwayne/learntla-v2.git
python -m venv learntla-v2
cd learntla-v2
Scripts\activate
python -m pip install -r requirements.txt
Scripts\deactivate
```

### Linux/Mac OS X

Similar.
    

## Usage

### Build HTML

```
Scripts\activate
docs\make html
Scripts\deactivate
```

### Watcher.ps1

```
Requires `Install-Module -Name FSWatcherEngineEvent`
```
