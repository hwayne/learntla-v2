Remove-FileSystemWatcher -SourceIdentifier "learntla"
New-FileSystemWatcher -SourceIdentifier "learntla" -Path $PSScriptRoot -IncludeSubdirectories -Filter *.rst

$docs_path = "$PSScriptRoot\docs"

$stop = $true
Register-EngineEvent "stoptla" -Action {$stop = $false}
while($stop) {
    wait-event "learntla"
    remove-event "learntla"
    & "$PSScriptRoot\venv-sphinx\Scripts\sphinx-build.exe" $docs_path "$docs_path\_build\html"
}
