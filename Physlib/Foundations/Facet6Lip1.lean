/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Physlib.Foundations.Facet6Map
public import Physlib.Foundations.Facet6Base

/-!
# Per-block count-lattice Lipschitz lemma `facet6G_lip_1` (block 1)

Standalone module for the heavy per-block lattice-Lipschitz lemma of block 1: bumping the
1-th popcount coordinate by `1` (a lattice edge) changes at most one of the 18 output bits of
`Facet6.facet6G`.  Split into its own module so `lake build` compiles the ten blocks in parallel
over the cached `Facet6Map` `.olean`; `maxHeartbeats 0` gives the `decide +kernel` unlimited
budget.  The lemma is `public` in `Physlib.UndirectedMMICertificate` so the certificate file
refers to it unqualified exactly as before.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] public section

namespace Physlib.UndirectedMMICertificate

open Finset

lemma facet6G_lip_1 :
    ∀ n0 ≤ 3, ∀ n1 ≤ 2, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 3, ∀ n5 ≤ 1, ∀ n6 ≤ 1, ∀ n7 ≤ 1,
      ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (Facet6.facet6G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (Facet6.facet6G n0 (n1+1) n2 n3 n4 n5 n6 n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;>
    interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;>
    interval_cases n8 <;> interval_cases n9 <;> decide +kernel

end Physlib.UndirectedMMICertificate

end
