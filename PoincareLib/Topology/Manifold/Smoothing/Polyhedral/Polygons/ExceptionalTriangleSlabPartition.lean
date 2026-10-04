import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.ZeroApexPositivePart
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.GeometricResidualTriangle

/-!
# Collar and residual coverage of an original exceptional slab

Identify the original triangle's nonnegative part before
applying the explicit geometric residual partition. The
whole original closed slab is covered with exact common
upper edge. See Alexander 1924, pp. 6--8 and derivation 203.
-/

set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual exceptional collar triangle and its residual
triangle cover the complete original closed slab. Their
intersection is exactly the actual upper collar edge.
See Alexander pp. 6--8 and M76 derivation 203. -/
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
