/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Mathlib

/-!
# Shared boolean Hamming indicator `bdiff`

This tiny module owns the single boolean Hamming indicator `bdiff` (and its symmetry lemma
`bdiff_comm`) used both by `Physlib.Foundations.UndirectedMMICertificate` and by the ten
standalone per-block lattice-Lipschitz modules `Physlib.Foundations.Facet6Lip0 … Facet6Lip9`.
Keeping `bdiff` in one shared module lets the heavy `facet6G_lip_b` lemmas compile as independent
modules (in parallel, with unlimited heartbeats) over the cached `Facet6Map` `.olean`, while the
main certificate file still refers to the very same `bdiff` definition and lip lemma names.
-/

@[expose] public section

namespace Physlib.UndirectedMMICertificate

/-- The boolean Hamming indicator: `1` when the two booleans differ, `0` otherwise. -/
def bdiff (a b : Bool) : ℕ := if a ≠ b then 1 else 0

/-- `bdiff` is symmetric. -/
theorem bdiff_comm (a b : Bool) : bdiff a b = bdiff b a := by
  unfold bdiff; revert a b; decide

end Physlib.UndirectedMMICertificate

end
