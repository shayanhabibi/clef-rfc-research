# clef-rfc-research

Proposals for the [Clef language](https://clef-lang.com/spec/) whose claims are theorems checked by [Rocq](https://rocq-prover.org). Each RFC is a Rocq development: the design rules are definitions, the claims are theorems, and the prose is written in the comments between them.

The site is published at <https://shayanhabibi.github.io/clef-rfc-research/>.

This is research. It is not part of the Clef specification, and nothing here is accepted until it goes through the specification's change process.

## Layout

| Path | Holds |
|---|---|
| `proofs/_CoqProject` | One Rocq project for the spec assumptions and every RFC |
| `proofs/theories/Spec` | What every RFC may assume about Clef, as axioms and parameters that cite the specification |
| `proofs/theories/RFC0001` | RFC 0001: Closed-set type constraints |
| `proofs/theories/RFC0002` | RFC 0002: Type-case over several constrained variables |
| `research` | Research notes behind the RFCs, with their sources |
| `proofs/template` | The modules a new RFC starts from |
| `proofs/facts.json` | Types and assumptions captured from Rocq, for the site's hover cards and badges |
| `site` | The site: a [Nacara](https://github.com/shayanhabibi/Nacara) program using `Nacara.Plugin.Rocq` from [FSharp.Data.Rocq](https://github.com/ranvier-org/FSharp.Data.Rocq) and `Partas.Nacara.Theme` |

## Start an RFC

```bash
bash proofs/new-rfc.sh 0002 "Tagged anonymous sums"
```

The site's [Writing an RFC](site/pages/process/writing.md) page describes the comment syntax and the standard a claim must meet.

## Build

Check the proofs, with Rocq 9.1 on the path:

```bash
bash proofs/build.sh
```

Capture the types and assumptions. The value of `--rocq` is the command that starts Rocq:

```bash
dotnet run --project site -- rocq-capture --rocq "rocq" --out ../proofs/facts.json
```

Build the site into `site/output`:

```bash
dotnet run --project site -- build --strict
```

The `.glob` files and `proofs/facts.json` are committed, so the last step needs only the .NET SDK. It fails when either is older than its source. CI runs that step alone and publishes the result to GitHub Pages. It does not run Rocq, so compile and capture before committing a change to a `.v` file.
