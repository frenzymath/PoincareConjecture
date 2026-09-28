import PoincareConjecture.Proofs.M76.Mathlib.ZeroApexPositivePart
import PoincareConjecture.Proofs.M76.Mathlib.GeometricResidualTriangle










set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exceptional_triangle_slab_partition (A : E →ᵃ[ℝ] ℝ) {q u v : E}
    (hq : A q = 0) (hu : A u < 0) {β : ℝ} (hβ : 0 < β) (hβv : β < A v)
    (hqw : q ≠ A.zeroCrossing u v) :
    (convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ∪
        convexHull ℝ (insert q ({A.edgeLevel (A.zeroCrossing u v) v β,
          A.edgeLevel q v β} : Set E)) =
      convexHull ℝ (insert q ({u, v} : Set E)) ∩ {x | A x ∈ Icc 0 β}) ∧
    (convexHull ℝ (insert q ({A.zeroCrossing u v,
          A.edgeLevel (A.zeroCrossing u v) v β} : Set E)) ∩
        convexHull ℝ (insert q ({A.edgeLevel (A.zeroCrossing u v) v β,
          A.edgeLevel q v β} : Set E)) =
      segment ℝ q (A.edgeLevel (A.zeroCrossing u v) v β)) := by
  have hv : 0 < A v := hβ.trans hβv
  have hw : A (A.zeroCrossing u v) = 0 := A.zeroCrossing_apply (hu.trans hv).ne
  obtain ⟨hunion, hinter⟩ := A.zeroApex_slab_partition hqw hq hw hβ hβv
  refine ⟨hunion.trans ?_, hinter⟩
  rw [← A.convexHull_zero_apex_pair_inter_nonneg hq hu hv]
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc]
  tauto

end AffineMap
