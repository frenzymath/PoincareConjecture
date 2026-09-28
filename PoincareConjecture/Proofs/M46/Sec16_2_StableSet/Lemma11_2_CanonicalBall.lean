import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SpatialBall
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CanonicalAnalytics
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M35.Thm12_28.CapScalarEstimates

set_option autoImplicit false

open Set Manifold
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

theorem metric_ball_subset_connectedComponent
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (x : M) (r : ℝ) :
    g.ball x r ⊆ connectedComponent x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro y hy
  obtain ⟨gamma, hzero, hone, hgamma, _⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hy
  exact (isPreconnected_Icc.image gamma hgamma.continuousOn).subset_connectedComponent
    ⟨0, ⟨le_rfl, zero_le_one⟩, hzero⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, hone⟩

theorem canonical_scalar_le_two_inv_sq_on_ball
    (S : RepairedControlledSchedulesData.{u}) (F : SurgeryFlowData.{u})
    (t : ℝ) (x : (F.slice t).carrier) {B r : ℝ}
    (hB : seedAnalyticConstant S ≤ B) (hr : 0 < r)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hcenter : (F.connection t).scalarCurvature x ≤ r⁻¹ ^ 2)
    (hcanonical : ∀ y ∈ (F.metric t).ball x (r / (8 * B)),
      r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature y →
        SurgeryCanonicalControl F t y F.parameters.epsilon S.setup.C) :
    ∀ y ∈ (F.metric t).ball x (r / (8 * B)),
      (F.connection t).scalarCurvature y ≤ 2 * r⁻¹ ^ 2 := by
  apply scalar_le_two_inv_sq_on_ball (F.metric t) (F.connection t)
    (M34.contMDiff_scalarCurvature (F.connection t))
    ((seedAnalyticConstant_pos S).trans_le hB) hr x hcenter
  intro y hy hhigh v hv
  have hcomponent := metric_ball_subset_connectedComponent (F.metric t) x
    (r / (8 * B)) hy
  have hnotpositive : ¬ SurgeryPositiveComponentAt F t y := by
    intro hpos
    apply hpositive
    intro z hz
    exact hpos z (by simpa only [connectedComponent_eq hcomponent] using hz)
  have h := canonical_analytic_on_nonpositive S F t y
    (hcanonical y hy hhigh) hnotpositive
  exact ((F.connection t).abs_scalar_directional_le_scalarGradientNorm y v hv).trans
    (h.2.1.trans (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg h.1.le _)))

end PoincareConjecture.Proofs.M46
