import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoveryAction
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurveEndpoints
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeCurve









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



theorem square_density_gauge_germ (j : G.gaugeCover.index)
    (theta : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (alpha : ℝ → G.gaugeCover.spatial j) (g : ℝ → G.Point) {C : Set ℝ} {s : ℝ}
    (hC : C ∈ 𝓝 s)
    (heq : g =ᶠ[𝓝 s] fun r => (G.gaugeCover.cylinder j).toSpacetime (theta r, alpha r))
    (htheta : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) theta s)
    (halpha : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 3) alpha s) :
    M14.squareCurveDensity G g C s =
      2 * s ^ 2 * horizontalScalarCurvature G.leafwise
        ((G.gaugeCover.cylinder j).toSpacetime (theta s, alpha s)) +
      (1 / 2 : ℝ) * ((G.gaugeCover.metric j).metric (theta s).val).inner (alpha s)
        (deriv (fun r => (alpha r).val) s) (deriv (fun r => (alpha r).val) s) := by
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel 3)
  unfold M14.squareCurveDensity M14.projectedCurveVelocityWithin
  rw [mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel 3) hC,
    hd, heq.eq_of_nhds]
  change 2 * s ^ 2 * horizontalScalarCurvature G.leafwise _ + (1 / 2 : ℝ) *
    G.spacetime.horizontalMetric.inner _
      (M14.projectedCurveVelocity G
        (fun r => (G.gaugeCover.cylinder j).toSpacetime (theta r, alpha r)) s)
      (M14.projectedCurveVelocity G
        (fun r => (G.gaugeCover.cylinder j).toSpacetime (theta r, alpha r)) s) = _
  rw [M14.gaugeCurve_projectedVelocity j theta alpha htheta halpha,
    ← (G.gaugeCover.metric j).metric_eq]





theorem gauge_recovery_piece_action (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (j : G.gaugeCover.index) {a b : ℝ} (hab : a ≤ b)
    (theta : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point)
    (alpha : ℝ → G.gaugeCover.spatial j) (g : ℝ → G.Point) {C : Set ℝ}
    (hsub : Icc a b ⊆ C)
    (htheta : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) 1 theta (Icc a b))
    (halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) 1 alpha (Icc a b))
    (heq : EqOn g (fun r => (G.gaugeCover.cylinder j).toSpacetime (theta r, alpha r))
      (Icc a b))
    (hint : IntervalIntegrable (M14.squareCurveDensity G g C) volume a b)
    (v : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b)
    (hv : (v : ℝ → EuclideanSpace ℝ (Fin 3)) =ᵐ[volume.restrict (Icc a b)]
      deriv (fun r => (alpha r).val)) :
    gaugeCylinderAction j theta alpha v = ∫ s in a..b, M14.squareCurveDensity G g C s := by
  let V := fun s => 2 * s ^ 2 * horizontalScalarCurvature G.leafwise
    ((G.gaugeCover.cylinder j).toSpacetime (theta s, alpha s))
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hscalar := H.scalar_smooth.continuous.comp
    (G.gaugeCover.cylinder j).smooth.continuous
  have hV : ContinuousOn V (Icc a b) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (hscalar.comp_continuousOn (htheta.continuousOn.prodMk halpha.continuousOn))
  have hVint : IntervalIntegrable V volume a b := hV.intervalIntegrable_of_Icc hab
  have hkin : (∫ s in a..b, (1 / 2 : ℝ) *
      ((G.gaugeCover.metric j).metric (theta s).val).inner (alpha s) (v s) (v s)) =
      ∫ s in a..b, M14.squareCurveDensity G g C s - V s := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    have hmem : ∀ᵐ s ∂volume.restrict (Icc a b), s ∈ Ioo a b := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hv, hmem] with s hs hsI
    have hsg : C ∈ 𝓝 s := mem_of_superset (isOpen_Ioo.mem_nhds hsI)
      (Ioo_subset_Icc_self.trans hsub)
    have hrec : g =ᶠ[𝓝 s] fun r =>
        (G.gaugeCover.cylinder j).toSpacetime (theta r, alpha r) := by
      filter_upwards [isOpen_Ioo.mem_nhds hsI] with r hr
      exact heq (Ioo_subset_Icc_self hr)
    have ht := ((htheta s (Ioo_subset_Icc_self hsI)).contMDiffAt
      (Icc_mem_nhds hsI.1 hsI.2)).mdifferentiableAt (by simp)
    have ha := ((halpha s (Ioo_subset_Icc_self hsI)).contMDiffAt
      (Icc_mem_nhds hsI.1 hsI.2)).mdifferentiableAt (by simp)
    rw [square_density_gauge_germ j theta alpha g hsg hrec ht ha, hs]
    exact (add_sub_cancel_left _ _).symm
  unfold gaugeCylinderAction
  rw [hkin, intervalIntegral.integral_sub hint hVint]
  exact sub_add_cancel _ _

end PoincareConjecture.Proofs.M46
