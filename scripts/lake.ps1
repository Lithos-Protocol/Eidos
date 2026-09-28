# Use the project-local Windows toolchain when present, otherwise the installed Lake.
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path $PSScriptRoot -Parent
$toolchain = (Get-Content -Raw (Join-Path $projectRoot 'lean-toolchain')).Trim()
$version = $toolchain.Split(':')[-1].TrimStart('v')
$localLake = Join-Path $projectRoot ".tools\lean-$version-windows\bin\lake.exe"
if (Test-Path -LiteralPath $localLake) {
    $lakeCommand = $localLake
} else {
    $lakeCommand = (Get-Command lake -ErrorAction Stop).Source
}
Push-Location $projectRoot
try {
    & $lakeCommand @args
    $lakeExitCode = $LASTEXITCODE
} finally {
    Pop-Location
}
exit $lakeExitCode
