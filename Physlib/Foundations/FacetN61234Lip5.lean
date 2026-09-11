/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Physlib.Foundations.FacetN61234Map
public import Physlib.Foundations.Facet6Base

/-!
# Per-block count-lattice Lipschitz lemma `facet1234G_lip_5` (block 5)

Bumping the block-5 popcount by `1` (a lattice edge) changes at most one output bit of the
count-lattice contraction map `facet1234G`.  A finite `decide +kernel` over the count-lattice,
split into its own module for parallel compilation over the cached `FacetN61234Map` `.olean`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] public section

namespace Physlib.UndirectedMMICertificate

open Finset

lemma facet1234G_lip_5 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 3, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 0, ∀ n6 ≤ 1, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1, ∀ n10 ≤ 1,
    (∑ j, bdiff (facet1234G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 j)
                (facet1234G n0 n1 n2 n3 n4 (n5+1) n6 n7 n8 n9 n10 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9 n10 h10
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> interval_cases n10 <;> decide +kernel

end Physlib.UndirectedMMICertificate

end
