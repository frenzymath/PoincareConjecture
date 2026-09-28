import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.OpenCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




theorem intrinsicOpenMetric_edist_eq_of_ambient_ball_subset
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p q : U)
    {r : ℝ} (hball : g.ball (p : M) r ⊆ (U : Set M))
    (hq : g.edist (p : M) (q : M) < ENNReal.ofReal r) :
    (intrinsicOpenMetric g U).edist p q = g.edist (p : M) (q : M) := by
  apply le_antisymm
  · by_contra hnot
    have hlt : g.edist (p : M) (q : M) <
        min ((intrinsicOpenMetric g U).edist p q) (ENNReal.ofReal r) :=
      lt_min (lt_of_not_ge hnot) hq
    obtain ⟨s, _, hs, hsmin⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
    have hsmall : g.ball (p : M) s ⊆ (U : Set M) := by
      intro z hz
      exact hball (hz.trans (lt_of_lt_of_le hsmin (min_le_right _ _)))
    have hqin : q ∈ (intrinsicOpenMetric g U).ball p s := by
      rw [intrinsicOpenMetric_ball_eq_preimage g U p hsmall]
      exact hs
    exact (not_lt_of_ge (lt_of_lt_of_le hsmin (min_le_left _ _)).le) hqin
  · rw [intrinsicOpenMetric_edist]
    exact g.edist_le_intrinsicEDist _ _ _

variable [T2Space M]



theorem intrinsicOpenMetric_edist_eq_of_intrinsic_regular
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M) (p q : U)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g U) r)
    (hq : (intrinsicOpenMetric g U).edist p q < ENNReal.ofReal r) :
    (intrinsicOpenMetric g U).edist p q = g.edist (p : M) (q : M) := by
  apply intrinsicOpenMetric_edist_eq_of_ambient_ball_subset g U p q
    (ambient_ball_subset_open_of_intrinsic_regular g U p hp)
  rw [intrinsicOpenMetric_edist] at hq
  exact (g.edist_le_intrinsicEDist _ _ _).trans_lt hq




theorem intrinsicOpenMetric_edist_eq_on_nested_regular_image
    (g : RiemannianMetric 3 M) (U W : TopologicalSpace.Opens M)
    (hWU : (W : Set M) ⊆ (U : Set M)) (p q : W)
    {r : ℝ} (hp : p ∈ regularPoints (intrinsicOpenMetric g W) r)
    (hq : (intrinsicOpenMetric g W).edist p q < ENNReal.ofReal r) :
    (intrinsicOpenMetric g U).edist ⟨p, hWU p.property⟩ ⟨q, hWU q.property⟩ =
      (intrinsicOpenMetric g W).edist p q := by
  have heq := intrinsicOpenMetric_edist_eq_of_intrinsic_regular g W p q hp hq
  rw [intrinsicOpenMetric_edist] at heq
  rw [intrinsicOpenMetric_edist, intrinsicOpenMetric_edist]
  apply le_antisymm (intrinsicEDist_mono_of_subset hWU)
  rw [heq]
  exact g.edist_le_intrinsicEDist _ _ _

end PoincareConjecture.M28
