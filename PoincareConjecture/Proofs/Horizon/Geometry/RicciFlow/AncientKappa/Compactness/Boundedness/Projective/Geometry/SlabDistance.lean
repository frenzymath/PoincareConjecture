import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CylinderCover

variable {M : Type*} [TopologicalSpace M] [T2Space M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

omit [ConnectedSpace M] in

theorem toReal_edist_center_le
    (g : RiemannianMetric 3 M) (Φ : RoundCylinderSpace → M)
    {ε r : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) (hr : 0 < r)
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g Φ z v w))
    (q₀ : UnitTwoSphere) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    (g.edist (Φ z) (Φ (q₀, 0))).toReal ≤
      (2 * |z.2| + 4 * (Real.pi + 1)) * r := by
  have hzero : (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr hε), inv_pos.mpr hε⟩
  have hd := (g.edist_le_intrinsicEDist _ (Φ z) (Φ (q₀, 0))).trans
    (intrinsicEDist_cylinderCover_le_axial_add g Φ hε (by positivity)
      hΦ hclose hz hzero)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  simp only [zero_sub, abs_neg] at hreal
  have hs : Real.sqrt ((1 + ε) / r⁻¹ ^ 2) ≤ 2 * r := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_eq_mul_inv, inv_pow, inv_inv]
    nlinarith [sq_nonneg r]
  have hs2 : Real.sqrt 2 ≤ 2 := by
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  calc
    _ ≤ Real.sqrt ((1 + ε) / r⁻¹ ^ 2) *
        (|z.2| + Real.sqrt 2 * (Real.pi + 1)) := hreal
    _ ≤ (2 * r) * (|z.2| + 2 * (Real.pi + 1)) :=
      mul_le_mul hs (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hs2 (by positivity))) (by positivity) (by positivity)
    _ = _ := by ring

end PoincareConjecture.CylinderCover
