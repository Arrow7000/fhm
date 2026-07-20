import FHM.Surface.Lex
import Lean.Data.Json

/-!
# TextMate grammar exporter

Emits `editors/vscode/syntaxes/fhm.tmLanguage.json` from the live lexer tables
in `Surface.Lex` (keywords, bool lits, ops, punct). Comment / string / ident
patterns mirror the lexer but are regex approximations (TextMate cannot run
`Unicode.isAlphabetic`).
-/

open Surface.Lex
open Lean

/-- Escape a string for use inside a TextMate Oniguruma alternation. -/
def regexEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++
      match c with
      | '\\' | '.' | '*' | '+' | '?' | '^' | '$' | '{' | '}' | '(' | ')'
      | '|' | '[' | ']' | '/' => s!"\\{c}"
      | _ => String.singleton c

/-- Alternation of literal spellings (callers pass longest-first lists). -/
def regexAlt (xs : List String) : String :=
  String.intercalate "|" (xs.map regexEscape)

def pattern (name match_ : String) : Json :=
  Json.mkObj [("name", Json.str name), ("match", Json.str match_)]

def tmLanguage : Json :=
  let kwAlt := regexAlt keywordSurfaces
  let boolAlt := regexAlt boolLitSurfaces
  let opAlt := regexAlt binOpSurfaces
  let punctAlt := regexAlt punctSurfaces
  let identCont := "[\\p{L}\\p{N}\\p{M}_]"
  let identStart := "[\\p{L}]"
  Json.mkObj [
    ("$schema", Json.str
      "https://raw.githubusercontent.com/martinring/tmlanguage/master/tmlanguage.json"),
    ("name", Json.str "FHM"),
    ("scopeName", Json.str "source.fhm"),
    ("patterns", Json.arr #[
      Json.mkObj [("include", Json.str "#comments")],
      Json.mkObj [("include", Json.str "#strings")],
      Json.mkObj [("include", Json.str "#chars")],
      Json.mkObj [("include", Json.str "#keywords")],
      Json.mkObj [("include", Json.str "#booleans")],
      Json.mkObj [("include", Json.str "#numbers")],
      Json.mkObj [("include", Json.str "#ctors")],
      Json.mkObj [("include", Json.str "#identifiers")],
      Json.mkObj [("include", Json.str "#operators")],
      Json.mkObj [("include", Json.str "#punctuation")]
    ]),
    ("repository", Json.mkObj [
      ("comments", Json.mkObj [
        ("patterns", Json.arr #[
          Json.mkObj [
            ("name", Json.str "comment.line.double-dash.fhm"),
            ("match", Json.str "--.*$")
          ],
          Json.mkObj [
            ("name", Json.str "comment.block.fhm"),
            ("begin", Json.str "\\{-"),
            ("end", Json.str "-\\}"),
            ("patterns", Json.arr #[
              Json.mkObj [
                ("match", Json.str "\\{-"),
                ("name", Json.str "comment.block.fhm")
              ],
              Json.mkObj [
                ("match", Json.str "-\\}"),
                ("name", Json.str "comment.block.fhm")
              ]
            ])
          ]
        ])
      ]),
      ("strings", Json.mkObj [
        ("name", Json.str "string.quoted.double.fhm"),
        ("begin", Json.str "\""),
        ("end", Json.str "\""),
        ("patterns", Json.arr #[
          Json.mkObj [
            ("name", Json.str "constant.character.escape.fhm"),
            ("match", Json.str "\\\\[ntr\\\\\"']")
          ]
        ])
      ]),
      ("chars", pattern "string.quoted.single.fhm"
        "'(?:[^'\\\\]|\\\\[ntr\\\\\"'])'"),
      ("keywords", pattern "keyword.control.fhm" ("\\b(?:" ++ kwAlt ++ ")\\b")),
      ("booleans", pattern "constant.language.boolean.fhm" ("\\b(?:" ++ boolAlt ++ ")\\b")),
      ("numbers", pattern "constant.numeric.integer.fhm" "-?\\b[0-9]+\\b"),
      ("ctors", pattern "entity.name.type.fhm"
        ("\\b\\p{Lu}" ++ identCont ++ "*")),
      ("identifiers", pattern "variable.other.fhm"
        ("\\b" ++ identStart ++ identCont ++ "*")),
      ("operators", pattern "keyword.operator.fhm" ("(?:" ++ opAlt ++ ")")),
      ("punctuation", pattern "punctuation.fhm" ("(?:" ++ punctAlt ++ ")"))
    ])
  ]

def tablesJson : Json :=
  Json.mkObj [
    ("keywords", Json.arr (keywordSurfaces.toArray.map Json.str)),
    ("boolLits", Json.arr (boolLitSurfaces.toArray.map Json.str)),
    ("operators", Json.arr (binOpSurfaces.toArray.map Json.str)),
    ("punctuation", Json.arr (punctSurfaces.toArray.map Json.str))
  ]

def usage : String :=
  "usage: fhm_grammar [--tables]\n\
   default: write TextMate grammar JSON to stdout\n\
   --tables: write keyword/op/punct tables JSON to stdout"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.println (tmLanguage.pretty)
    return 0
  | ["--tables"] =>
    IO.println (tablesJson.pretty)
    return 0
  | _ =>
    IO.eprintln usage
    return 1
