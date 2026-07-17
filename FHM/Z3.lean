import FHM.Z3.Atom
import FHM.Z3.Query
import FHM.Z3.Encode
import FHM.Z3.Parse
import FHM.Z3.Oracle
import FHM.Z3.Process
import FHM.Z3.Examples

/-!
# FHM — Z3 oracle (entry point)

Subprocess-backed SMT oracle for bounded-list sketch problems. See
`FHM/BLSketch.lean` §5 for the problem-specific bridge.

## TCB

* `decide_verified_sound`, `decide_witness_sound`, `decide_sat_sound` in `Oracle.lean`
* Correctness of `Encode` / `Parse`
* The `z3` binary on PATH (via `z3RunImpl` / `Process.runZ3`)
* `unsafeBaseIO` referential-transparency assumption
-/

namespace FHM.Z3
end FHM.Z3
