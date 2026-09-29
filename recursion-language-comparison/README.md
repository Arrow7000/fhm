# Recursive polymorphism comparison

This corpus separates each language's accepted explicitly polymorphic case from the
nearby case that remains monomorphic. It exists to avoid the ambiguous shorthand
“language X supports polymorphic recursion”.

Run every case without installing the compilers globally:

```sh
nix-shell recursion-language-comparison/shell.nix \
  --run 'bash recursion-language-comparison/check.sh'
```

The checker expects:

| Language | Accepted | Rejected boundary |
|---|---|---|
| OCaml | Recursive function with an explicit `'a.` scheme | Ordinary `'a` parameter/result constraints do not introduce a recursive scheme |
| Haskell | Recursive function with a complete signature | The same body without a signature is inferred at one recursive monotype |
| F# | Recursive function with an explicit `<'T>` parameter | An ordinary `'T` annotation becomes constrained by recursive uses |
| Elm | Other members of a recursive cycle instantiate an annotated function differently | The function cannot instantiate its own annotation differently; an unannotated group is also monomorphic |
| Standard ML | A recursive function is generalized after its declaration exits | Calls during the recursive declaration share one monotype, even with an explicit scoped type variable |

These are deliberately small typechecking probes, not runtime tests. Expected failures
print their real compiler diagnostics. Compiler versions come from the selected
`nixpkgs` revision and are printed by the script.

FHM's intended boundary is illustrated separately in
[`../scratch/hm-recursion-boundary.fhm`](../scratch/hm-recursion-boundary.fhm). It is
uniformly monomorphic across the entire dependency SCC, making it stricter than Elm's
annotated-sibling rule and closer to Standard ML's recursive environment.
