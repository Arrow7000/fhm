import FHM.Unverified.Live

-- Exercise the guard directly, including trees too deep to inspect recursively.
private def nestedRuntime (depth : Nat) : Expr := Id.run do
  let mut e : Expr := .primLit .unit
  for _ in [:depth] do
    e := .app (.ctor ⟨"Box"⟩) e
  return e

#guard withinEvaluationDepth (nestedRuntime 511)
#guard !withinEvaluationDepth (nestedRuntime 512)
#guard !withinEvaluationDepth (nestedRuntime 10000)
#guard !withinEvaluationDepth (.primLit .unit) 0
#guard withinEvaluationDepth (.primLit .unit) 1

-- Inactive children must be covered: substitution and printing visit these too.
#guard !withinEvaluationDepth (.lambda none (nestedRuntime 512))
#guard !withinEvaluationDepth (.letIn none (nestedRuntime 512) (.primLit .unit))
#guard !withinEvaluationDepth (.match_ (.ctor ⟨"Box"⟩) [(.wildcard, nestedRuntime 512)])
#guard !withinEvaluationDepth (.letRec [none] [nestedRuntime 512] (.primLit .unit))
#guard withinEvaluationDepth (.letRec [none] [.lambda none (.var 0)] (.primLit .unit))

-- Guard even zero-fuel/value paths before the recursive isValue check or printing.
#guard (match evalCounting 0 (nestedRuntime 512) 7 with
  | .tooDeep n => n == 7
  | _ => false)
#guard (match evalCounting 10 (.lambda none (nestedRuntime 512)) 0 with
  | .tooDeep n => n == 0
  | _ => false)
#guard (match evalCountingUnsafe (.lambda none (nestedRuntime 512)) 0 with
  | .tooDeep n => n == 0
  | _ => false)
#guard (match evalCounting 0 (.primLit .unit) 0 with
  | .value _ n => n == 0
  | _ => false)
