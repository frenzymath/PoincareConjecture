import PoincareConjecture.Proofs.M76.Mathlib.ExceptionalTriangleSlabPartition
import PoincareConjecture.Proofs.M76.Mathlib.ResidualOppositeEdge
import PoincareConjecture.Proofs.M76.Mathlib.ResidualLevelScaling

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exceptional_collar_residual_contact_homothety (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) (hu : A u < 0) {β c : ℝ} (hβ : 0 < β) (hβv : β < A v)
    (hqw : q ≠ A.zeroCrossing u v) (hc : c ∈ Icc 0 β) :
    (convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ∩
        convexHull ℝ (insert q ({A.edgeLevel (A.zeroCrossing u v) v β,
          A.edgeLevel q v β} : Set E))) ∩ {x | A x = c} =
      homothety q (c / β) '' (segment ℝ u v ∩ {x | A x = β}) := by
  let w := A.zeroCrossing u v
  let p := A.edgeLevel w v β
  have hv : 0 < A v := hβ.trans hβv
  have hw : A w = 0 := A.zeroCrossing_apply (hu.trans hv).ne
  have hpA : A p = β := A.apply_edgeLevel (by rw [hw]; exact hv.ne') β
  have hpseg : p ∈ segment ℝ u v :=
    ((A.exceptional_residual_opposite_edge_intersection hq hu hβ hβv hqw).symm.subset
      (mem_singleton p)).2
  have hsection : segment ℝ u v ∩ {x | A x = β} = {p} := by
    ext x
    constructor
    · intro hx
      have hspan (y : E) (hy : y ∈ segment ℝ u v) :
          y ∈ affineSpan ℝ ({u, v} : Set E) :=
        convexHull_subset_affineSpan _ (by simpa only [convexHull_pair] using hy)
      exact mem_singleton_iff.mpr
        ((A.eq_edgeLevel_of_mem_affineSpan (hu.trans hv).ne' (hspan x hx.1) hx.2).trans
          (A.eq_edgeLevel_of_mem_affineSpan (hu.trans hv).ne' (hspan p hpseg) hpA).symm)
    · rintro rfl
      exact ⟨hpseg, hpA⟩
  rw [(A.exceptional_triangle_slab_partition hq hu hβ hβv hqw).2, hsection,
    ← convexHull_pair]
  simpa only [convexHull_singleton] using
    A.convexHull_insert_level_homothety hq (singleton_nonempty p) hβ
      (fun x hx => (mem_singleton_iff.mp hx) ▸ hpA) hc

end AffineMap
