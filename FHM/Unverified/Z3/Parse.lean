import FHM.Z3.Query
import FHM.Z3.Encode

/-!
# FHM — Z3 stdout → Verdict

Adapted from Percissus.Fresh.Z3.
-/

namespace FHM.Z3
namespace Parse

private def trim (s : String) : String := s.trim

private def firstWord (out : String) : String :=
  let trimmed := trim out
  match trimmed.splitOn "\n" with
  | [] => ""
  | l :: _ => trim l

private def hasSubstr (s pat : String) : Bool :=
  if pat.isEmpty then true else (s.splitOn pat).length > 1

inductive ReplyHead where
  | sat
  | unsat
  | unknown (reason : String)
  | bad (line : String)
  deriving Repr, BEq

private def replyHead (out : String) : ReplyHead :=
  match firstWord out with
  | "sat" => .sat
  | "unsat" => .unsat
  | "unknown" =>
      if hasSubstr out "timeout" then .unknown "timeout"
      else if hasSubstr out "incomplete" then .unknown "incomplete"
      else .unknown "z3 reported unknown"
  | other =>
      if hasSubstr out "(error " then
        .bad (firstErrorLine out)
      else .bad other
where
  firstErrorLine (s : String) : String :=
    let lines := (trim s).splitOn "\n"
    match lines.find? (fun l => (trim l).startsWith "(error ") with
    | some l => trim l
    | none => firstWord s

private def unprefix (sym : String) : Option String := Id.run do
  let mut s := sym.trim
  if s.startsWith "|" && s.endsWith "|" && s.length ≥ 2 then
    s := (s.drop 1).dropRight 1
  if s.startsWith "fhm_" then
    return some (s.drop 4)
  return none

private partial def tokenise (s : String) : List String :=
  let charsOf (cs : List Char) : String := String.ofList cs
  let rec dropLine : List Char → List Char
    | [] => []
    | '\n' :: rest => rest
    | _ :: rest => dropLine rest
  let rec readDelim (delim : Char) (acc : List Char) : List Char → String × List Char
    | [] => (charsOf (delim :: acc.reverse), [])
    | c :: rest =>
        if c == delim then
          (charsOf (delim :: (acc.reverse ++ [delim])), rest)
        else readDelim delim (c :: acc) rest
  let rec readPlain (acc : List Char) : List Char → String × List Char
    | [] => (charsOf acc.reverse, [])
    | c :: rest =>
        if c == '(' || c == ')' || c.isWhitespace || c == ';' || c == '|' then
          (charsOf acc.reverse, c :: rest)
        else readPlain (c :: acc) rest
  let rec go (acc : List String) : List Char → List String
    | [] => acc.reverse
    | '(' :: rest => go ("(" :: acc) rest
    | ')' :: rest => go (")" :: acc) rest
    | c :: rest =>
        if c.isWhitespace then go acc rest
        else if c == ';' then go acc (dropLine rest)
        else if c == '|' then
          let (tok, rest') := readDelim '|' [] rest
          go (tok :: acc) rest'
        else
          let (tok, rest') := readPlain [c] rest
          go (tok :: acc) rest'
  go [] s.toList

private def parseNat? (tok : String) : Option Nat :=
  if tok.isEmpty then none
  else
    let cs := tok.toList
    if cs.all (·.isDigit) then some tok.toNat! else none

private def parseDefineFun? (toks : List String) : Option (Option (String × Nat) × List String) :=
  match toks with
  | "(" :: "define-fun" :: sym :: "(" :: ")" :: "Int" :: rest =>
      match rest with
      | n :: ")" :: rest' =>
          match parseNat? n with
          | some v =>
              match unprefix sym with
              | some name => some (some (name, v), rest')
              | none      => some (none, rest')
          | none => some (none, rest')
      | "(" :: "-" :: _ :: ")" :: ")" :: rest' =>
          some (none, rest')
      | _ => none
  | _ => none

private partial def collectModel (toks : List String) : List (String × Nat) :=
  go toks
where
  go : List String → List (String × Nat)
    | [] => []
    | toks =>
      match parseDefineFun? toks with
      | some (some entry, rest) => entry :: go rest
      | some (none, rest) => go rest
      | none =>
          match toks with
          | _ :: rest => go rest
          | [] => []

def parseModel (out : String) : List (String × Nat) :=
  let trimmed := trim out
  let body :=
    if trimmed.startsWith "sat" then
      (trimmed.drop 3).trim
    else trimmed
  collectModel (tokenise body)

private def parenBalance (s : String) : Int :=
  s.toList.foldl (init := 0) fun acc c =>
    if c = '(' then acc + 1
    else if c = ')' then acc - 1
    else acc

private def modelBodyWellFormed (out : String) : Bool :=
  let trimmed := trim out
  let body :=
    if trimmed.startsWith "sat" then (trimmed.drop 3).trim else trimmed
  parenBalance body = 0

def checkOutput (out : String) : Verdict :=
  match replyHead out with
  | .unsat => .verified
  | .sat   =>
      if modelBodyWellFormed out then .refuted (parseModel out)
      else .unknown "malformed counter-model body"
  | .unknown reason => .unknown reason
  | .bad line => .unknown s!"unparsed z3 reply: {line}"

def witnessOutput (unknowns : List String) (out : String) : Verdict :=
  match replyHead out with
  | .sat =>
      if modelBodyWellFormed out then
        let model := parseModel out
        let binding := model.filter fun (name, _) => unknowns.contains name
        .witness binding
      else .unknown "malformed witness model body"
  | .unsat => .unknown "z3 reports no witness exists"
  | .unknown reason => .unknown reason
  | .bad line => .unknown s!"unparsed z3 reply: {line}"

def satOutput (out : String) : SatVerdict :=
  match replyHead out with
  | .sat =>
      if modelBodyWellFormed out then .sat (parseModel out)
      else .unknown "malformed model body"
  | .unsat => .unsat
  | .unknown reason => .unknown reason
  | .bad line => .unknown s!"unparsed z3 reply: {line}"

end Parse
end FHM.Z3
