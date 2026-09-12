/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Physlib.Foundations.FacetN622Map
public import Physlib.Foundations.Facet6Base

/-!
# Per-block count-lattice Lipschitz lemma `facet22G_lip_1` (block 1)

Bumping the block-1 popcount by `1` (a lattice edge) changes at most one output bit of the
count-lattice contraction map `facet22G`.  A finite `decide +kernel` over the count-lattice,
split into its own module for parallel compilation over the cached `FacetN622Map` `.olean`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] public section

namespace Physlib.UndirectedMMICertificate

open Finset

lemma facet22G_lip_1 :
    ∀ n0 ≤ 2, ∀ n1 ≤ 0, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 1, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1, ∀ n10 ≤ 1, ∀ n11 ≤ 1, ∀ n12 ≤ 1,
    (∑ j, bdiff (facet22G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 j)
                (facet22G n0 (n1+1) n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9 n10 h10 n11 h11 n12 h12
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> interval_cases n10 <;> interval_cases n11 <;> interval_cases n12 <;> decide +kernel

end Physlib.UndirectedMMICertificate

end
