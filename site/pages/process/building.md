---
title: Building
---

The site is built from compiled proofs that are committed to the repository. Checking the proofs needs Rocq. Building the site needs only the .NET SDK.

## Check the proofs

With Rocq 9.1 on the path:

```bash
bash proofs/build.sh
```

This compiles every module in the order `proofs/_CoqProject` lists them, and stops at the first proof that fails. Each module gets a `.vo` and a `.glob` beside it. A `.glob` is committed. A `.vo` is not.

## Capture the facts

The types on hover cards and the assumption badges come from Rocq, through a file that is committed:

```bash
dotnet run --project site -- rocq-capture --rocq "rocq" --out ../proofs/facts.json
```

The value of `--rocq` is the command that starts Rocq. Where Rocq is installed in WSL and the .NET SDK on Windows, a wrapper works, given the full path of `opam` inside WSL:

```bash
dotnet run --project site -- rocq-capture --rocq "wsl.exe -e /home/you/.local/bin/opam exec -- rocq" --out ../proofs/facts.json
```

## Build the site

```bash
dotnet run --project site -- build --strict
```

The output is `site/output`. The build fails when a `.glob` or `facts.json` is older than its source, so a site cannot be published from sources that changed after they were compiled.

## What CI does

The workflow in `.github/workflows/pages.yml` builds the site from the committed files on every push to `main`, and publishes it to GitHub Pages. It does not run Rocq. The freshness check above ties the published pages to the sources that were compiled.
