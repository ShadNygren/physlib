/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren (with Claude Code)
-/
module

public import Physlib.Foundations.FacetN67451Map
public import Physlib.Foundations.Facet6Base

/-!
# Per-block count-lattice Lipschitz lemmas for facet 7451

Bumping any one block popcount by `1` (a lattice edge) changes at most one output bit of the
count-lattice contraction map `facet7451G`.  Each is a finite `decide +kernel` over the
count-lattice.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] public section

namespace Physlib.UndirectedMMICertificate

open Finset


lemma facet7451G_lip_0 :
    ∀ n0 ≤ 0, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G (n0+1) n1 n2 n3 n4 n5 n6 n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_1 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 0, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 (n1+1) n2 n3 n4 n5 n6 n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_2 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 0, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 (n2+1) n3 n4 n5 n6 n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_3 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 0, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 n2 (n3+1) n4 n5 n6 n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_4 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 0, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 n2 n3 (n4+1) n5 n6 n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_5 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 0, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 n2 n3 n4 (n5+1) n6 n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_6 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 2, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 n2 n3 n4 n5 (n6+1) n7 n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_7 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 0, ∀ n8 ≤ 1, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 n2 n3 n4 n5 n6 (n7+1) n8 n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_8 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 0, ∀ n9 ≤ 1,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 (n8+1) n9 j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

lemma facet7451G_lip_9 :
    ∀ n0 ≤ 1, ∀ n1 ≤ 1, ∀ n2 ≤ 1, ∀ n3 ≤ 1, ∀ n4 ≤ 1, ∀ n5 ≤ 1, ∀ n6 ≤ 3, ∀ n7 ≤ 1, ∀ n8 ≤ 1, ∀ n9 ≤ 0,
    (∑ j, bdiff (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 j)
                (facet7451G n0 n1 n2 n3 n4 n5 n6 n7 n8 (n9+1) j)) ≤ 1 := by
  intro n0 h0 n1 h1 n2 h2 n3 h3 n4 h4 n5 h5 n6 h6 n7 h7 n8 h8 n9 h9
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> interval_cases n4 <;> interval_cases n5 <;> interval_cases n6 <;> interval_cases n7 <;> interval_cases n8 <;> interval_cases n9 <;> decide +kernel

end Physlib.UndirectedMMICertificate

end
