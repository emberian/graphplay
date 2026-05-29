/-
# Graphplay.TacticsInit

**Attribute / rule-set declarations for `Graphplay.Tactics`.**

Lean's `register_simp_attr` and `declare_aesop_rule_sets` commands are *not*
visible in the file that declares them — they only become usable in *importing*
files (the elaborator emits this exact diagnostic).  This tiny leaf module
therefore holds only the declarations; `Graphplay.Tactics` imports it and is the
single place that *populates* and *uses* them.

The named sets:

* `graphplay_herm`     — `star`/`conjTranspose` pushing for Hermitian goals,
* `graphplay_modulus`  — unit-modulus / Born-rule `‖·‖ = 1` rewrites,
* `graphplay_equitable`— equitable-partition cell-sum shape rewrites,
* aesop rule set `Graphplay` — Hermitian / membership structural rules.

No global `@[simp]` is registered here; only the *new* named attributes are
created.  Lemmas are tagged into them from `Graphplay.Tactics`.
-/

import Mathlib.Tactic

/-- Simp set for Hermitian / `star`-pushing goals. -/
register_simp_attr graphplay_herm

/-- Simp set for unit-modulus / Born-rule goals. -/
register_simp_attr graphplay_modulus

/-- Simp set for equitable-partition cell-sum goals. -/
register_simp_attr graphplay_equitable

-- Aesop rule set seeded for Hermitian / membership structural goals.
declare_aesop_rule_sets [Graphplay]
