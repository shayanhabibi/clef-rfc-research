module Rfc.Site

open System
open System.IO
open System.Text.RegularExpressions
open Feliz.ViewEngine
open FSharp.Data.Rocq.Project
open FSharp.Data.Rocq.Structure
open Nacara.Core
open Nacara.Plugins
open Partas.Nacara.Theme

let private baseUrl =
    match Environment.GetEnvironmentVariable "SITE_BASE_URL" with
    | null
    | "" -> "/"
    | value -> value

/// The Rocq project holding the spec assumptions and every RFC, relative to this directory.
let private proofs = "../proofs/_CoqProject"

/// Where the plugin publishes the project: a page per module and the Guarantees page.
let private proofsRoot = "proofs"

/// The research notes behind the RFCs, relative to this directory. Each is published as a page.
let private research = "../research"

let private rocqOptions =
    Rocq.defaults
    |> Rocq.project proofs
    |> Rocq.facts (Some "../proofs/facts.json")
    |> Rocq.config (Some "../proofs/navigator.json")
    |> Rocq.root proofsRoot
    |> Rocq.home (Some ("All RFCs", baseUrl))

/// One RFC, read from the compiled project.
type private Rfc =
    {
        Number: string
        Title: string
        Stage: string
        Overview: string
        Theorems: int
        Lemmas: int
        Unproved: int
        Assumptions: int
    }

let private isProved (declaration: Declaration) =
    declaration.Proofs
    |> Array.forall (fun proof -> proof.Ending <> ProofEnding.Admitted)

/// The number of axioms and parameters in the modules whose name starts with a prefix.
let private assumptionsIn (project: RocqProject) (prefix: string) =
    project.Declarations
    |> Array.filter (fun d ->
        project.Files[d.File].Module.StartsWith (prefix, StringComparison.Ordinal)
        && d.Declaration.Category = Category.Assumption
        // A Variable or Hypothesis of a section is discharged when the section closes.
        && List.contains d.Declaration.Keyword [ Some "Axiom"; Some "Axioms"; Some "Parameter"; Some "Parameters"; Some "Conjecture" ])
    |> Array.length

/// <summary>Every RFC of the project. An RFC is a directory of modules named <c>Clef.RFCnnnn.*</c> with an <c>Overview</c>.</summary>
let private rfcs (project: RocqProject) =
    project.Files
    |> Array.indexed
    |> Array.choose (fun (index, file) ->
        let m = Regex.Match (file.Module, @"^Clef\.RFC(\d+)\.Overview$")

        if m.Success then
            Some (index, file, m.Groups[1].Value)
        else
            None)
    |> Array.map (fun (_, file, number) ->
        let source = File.ReadAllText file.FullPath
        let title = Regex.Match (source, @"\(\*\*md # RFC \d+: (.+)")
        let stage = Regex.Match (source, @"\*\*Stage\*\* \| (.+?) \|")
        let prefix = $"Clef.RFC{number}."

        let proofsOf keyword =
            project.Declarations
            |> Array.filter (fun d ->
                project.Files[d.File].Module.StartsWith (prefix, StringComparison.Ordinal)
                && d.Declaration.Category = Category.Theorem
                && List.contains d.Declaration.Keyword keyword)

        let theorems = proofsOf [ Some "Theorem"; Some "Corollary" ]
        let lemmas = proofsOf [ Some "Lemma"; Some "Fact"; Some "Proposition"; Some "Remark" ]

        {
            Number = number
            Title =
                if title.Success then
                    title.Groups[1].Value.Trim ()
                else
                    file.Module
            Stage =
                if stage.Success then
                    stage.Groups[1].Value.Trim ()
                else
                    "Unknown"
            Overview = $"{baseUrl}{proofsRoot}/{file.Module}.html"
            Theorems = theorems |> Array.filter (_.Declaration >> isProved) |> Array.length
            Lemmas = lemmas |> Array.filter (_.Declaration >> isProved) |> Array.length
            Unproved =
                Array.append theorems lemmas
                |> Array.filter (_.Declaration >> isProved >> not)
                |> Array.length
            Assumptions = assumptionsIn project prefix
        })
    |> Array.sortBy _.Number

let private rfcTable (project: RocqProject) =
    let rows =
        rfcs project
        |> Array.map (fun rfc ->
            $"| [{rfc.Number}]({rfc.Overview}) | [{rfc.Title}]({rfc.Overview}) | {rfc.Stage} | {rfc.Theorems} | {rfc.Lemmas} | {rfc.Unproved} | {rfc.Assumptions} |")
        |> String.concat "\n"

    "| RFC | Title | Stage | Theorems proved | Lemmas proved | Unproved | Own assumptions |\n|---|---|---|---|---|---|---|\n"
    + rows

/// <summary>Writes <c>content</c> from <c>pages</c>, filling in the base URL, the RFC table and the count of spec assumptions.</summary>
let private weave () =
    let project =
        match load proofs with
        | Ok project -> project
        | Error failures ->
            failwith (
                "The Rocq project did not load. Run proofs/build.sh first.\n"
                + (failures
                   |> Array.map describeFailure
                   |> String.concat "\n")
            )

    if Directory.Exists "content" then
        Directory.Delete ("content", true)

    for source in Directory.GetFiles ("pages", "*.md", SearchOption.AllDirectories) do
        let target =
            Path.Combine ("content", Path.GetRelativePath ("pages", source))

        Directory.CreateDirectory (Path.GetDirectoryName target)
        |> ignore

        let text =
            (File.ReadAllText source)
                .Replace("<!-- rfcs -->", rfcTable project)
                .Replace("{{spec-assumptions}}", string (assumptionsIn project "Clef.Spec."))
                .Replace ("{{base}}", baseUrl)

        File.WriteAllText (target, text)

    // A research note is published as it is written: its first heading becomes the page title.
    for source in Directory.GetFiles (research, "*.md") do
        let text = File.ReadAllText source
        let heading = Regex.Match (text, @"\A# (.+?)\r?\n")

        if not heading.Success then
            failwith $"The research note {source} does not start with a heading."

        let title = heading.Groups[1].Value.Trim().Replace ("\"", "'")
        let target = Path.Combine ("content", "research", Path.GetFileName source)

        Directory.CreateDirectory (Path.GetDirectoryName target)
        |> ignore

        File.WriteAllText (target, $"---\ntitle: \"{title}\"\n---\n" + text.Substring heading.Length)

let private styles =
    """
.rfc-hero { padding-block: var(--nacara-space-8); text-align: center; }
.rfc-hero__title { margin: 0; font-size: clamp(2.25rem, 7vw, 3.5rem); overflow-wrap: anywhere; }
.rfc-hero__line { max-width: 42rem; margin: var(--nacara-space-4) auto 0; font-size: var(--nacara-font-size-lg); color: var(--nacara-text-muted); }
.rfc-hero__actions { display: flex; flex-wrap: wrap; justify-content: center; gap: var(--nacara-space-2); margin-top: var(--nacara-space-8); }
.rfc-button { display: inline-flex; align-items: center; min-height: 2.75rem; padding-inline: var(--nacara-space-4); border: 1px solid var(--nacara-border); border-radius: var(--nacara-radius); background: var(--nacara-bg-raised); color: var(--nacara-text); font-weight: 600; text-decoration: none; }
.rfc-button:hover { border-color: var(--nacara-primary); color: var(--nacara-text); text-decoration: none; }
.rfc-button--primary, .rfc-button--primary:hover { border-color: var(--nacara-primary); background: var(--nacara-primary); color: var(--nacara-primary-contrast); }
"""

let private theme =
    Theme.defaults
    |> Theme.navbar
        [
            NavbarLink ("Guarantees", $"/{proofsRoot}/index.html")
            NavbarSection ("Research", "research", "/research/")
            NavbarSection ("Process", "process", "/process/")
        ]
    |> Theme.navbarEnd
        [
            NavbarIcon ("GitHub", "https://github.com/shayanhabibi/clef-rfc-research", Icons.github)
        ]
    |> Theme.menu
        "process"
        [
            Menu.page "process/index.md"
            Menu.page "process/writing.md"
            Menu.page "process/assumptions.md"
            Menu.page "process/building.md"
        ]
    |> Theme.menu
        "research"
        (Menu.page "research/index.md"
         :: (Directory.GetFiles (Path.Combine (__SOURCE_DIRECTORY__, research), "*.md")
             |> Array.sort
             |> Array.map (fun note -> Menu.page $"research/{Path.GetFileName note}")
             |> List.ofArray))
    |> Theme.css styles
    |> Theme.footer (Html.p [ Html.text "Clef RFC research · Proofs checked by Rocq · Built with Nacara" ])

let private site () =
    Site.create "Clef RFC research"
    |> Site.baseUrl baseUrl
    |> Site.output "output"
    |> Site.noStaticFiles
    |> Markdown.register
    |> TreeSitter.register
    |> Rocq.register rocqOptions
    // A hosted build has no need to depend on other sites answering.
    |> LinkValidator.registerWith (fun options ->
        { options with
            CheckExternal = isNull (Environment.GetEnvironmentVariable "CI")
        })
    |> Theme.register theme
    |> Site.collection (Theme.docs theme "content")
    |> Site.collection (
        Rocq.collection "proofs" rocqOptions
        |> Collection.layout (Rocq.reader rocqOptions)
    )

[<EntryPoint>]
let main argv =
    Directory.SetCurrentDirectory __SOURCE_DIRECTORY__

    match List.ofArray argv with
    | "rocq-capture" :: _ -> Nacara.run (site ()) argv
    | _ ->
        weave ()
        Nacara.run (site ()) argv
