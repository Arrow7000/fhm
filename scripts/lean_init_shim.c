/*
 * Link-time shim: replaces lean_initialize() with the lighter
 * lean_initialize_runtime_module().
 *
 * Lean's compiler emits a main() that calls lean_initialize() — full
 * initialization of every Lean.* compiler module — whenever any Lean.*
 * module appears (non-meta) in the import closure (here: Lean.Data.Json).
 * That single call roots ~all of libLean through the linker's dead-strip.
 *
 * fhm only uses Lean.Json as a data structure; the per-module runtime
 * init chain (which still runs, unchanged) initializes everything fhm
 * actually imports. Linking this object BEFORE -lLean satisfies the
 * lean_initialize reference so the archive member never gets pulled.
 *
 * SAFETY: only valid while the program does no runtime metaprogramming
 * (no Lean.Environment / importModules / interpreter use). If that ever
 * changes, drop this shim — the failure mode is a loud crash at startup
 * or first use, not silent corruption.
 */
void lean_initialize_runtime_module(void);
void lean_initialize(void) { lean_initialize_runtime_module(); }
