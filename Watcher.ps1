Remove-FileSystemWatcher -SourceIdentifier "learntla"
New-FileSystemWatcher -SourceIdentifier "learntla" -Path $PSScriptRoot -IncludeSubdirectories -Filter *.rst

Remove-FileSystemWatcher -SourceIdentifier "cleanup"
New-FileSystemWatcher -SourceIdentifier "cleanup" -Path $PSScriptRoot -IncludeSubdirectories -Filter *.old
Register-EngineEvent -SourceIdentifier "cleanup" -Action {rm $event.Messagedata.FullPath}

$docs_path = "$PSScriptRoot\docs"

$Driver = Start-SeFirefox
Enter-SeUrl "$docs_path\_build\html\index.html" -Driver $Driver

while($true) {
    wait-event "learntla"
    remove-event "learntla"
    & "$PSScriptRoot\venv-sphinx\Scripts\sphinx-build.exe" -qT $docs_path "$docs_path\_build\html"
    Open-SeUrl -Refresh -Driver $Driver
}
