import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.SmallCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.EarlierVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  RicciFlow.smallCarrier RicciFlow.smallChartedSpace RicciFlow.smallIsManifold
  RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace RicciFlow.smallBorelSpace

theorem exists_pointedCompactnessHypotheses_of_finite_source_family
    {T B rho v : ℝ} (hT : 0 < T) (hrho : 0 < rho) (hv : 0 < v)
    (N : ℕ → Type u)
    [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    [∀ k, T3Space (N k)] [∀ k, SecondCountableTopology (N k)]
    [∀ k, ConnectedSpace (N k)]
    [∀ k, MeasurableSpace (N k)] [∀ k, BorelSpace (N k)]
    (G : ∀ k, RicciFlow 3 (N k) (Icc (-T) 0)) (p : ∀ k, N k)
    (hcurv : ∀ k, ∀ t ∈ Icc (-T) 0, ∀ x : N k,
      ((G k).connection t).curvatureTensorNorm x ≤ B)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal v ≤
      ((G k).metric 0).volumeMeasure (((G k).metric 0).ball (p k) rho))
    (hcompact : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      IsCompact (closure (((G k).metric 0).ball (p k) A))) :
    ∃ H : PointedRicciFlowCompactnessHypotheses 3 (-T / 2) (T / 2),
      ∀ k,
        let C := H.sequence.carrier k
        let : TopologicalSpace C.carrier := C.topologicalSpace
        let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
        let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
        ∃ e : C.carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N k,
          e (H.sequence.flow k).base = p k ∧
          ∀ (t : ℝ) (x : C.carrier) (a b : TangentSpace (𝓡 3) x),
            ((H.sequence.flow k).flow.metric t).inner x a b =
              ((G k).metric (t - T / 2)).inner (e x)
                (mfderiv (𝓡 3) (𝓡 3) e x a) (mfderiv (𝓡 3) (𝓡 3) e x b) := by
  classical
  let K : ℝ := max B 1
  let L : ℝ := (3 : ℝ) ^ 3 * K
  let E : ℝ := Real.exp (L * T)
  have hK : 0 ≤ K := zero_le_one.trans (le_max_right B 1)
  have hL : 0 ≤ L := mul_nonneg (by positivity) hK
  have hE : 0 < E := Real.exp_pos _
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
  have href : -(T / 2) ∈ Icc (-T) 0 := ⟨by linarith, by linarith⟩
  have hRic (k : ℕ) (t : ℝ) (ht : t ∈ Icc (-T) 0) (x : N k)
      (w : TangentSpace (𝓡 3) x) :
      |((G k).connection t).ricci x w w| ≤ L * ((G k).metric t).inner x w w := by
    have hQ : 0 ≤ ((G k).metric t).inner x w w := by
      by_cases hw : w = 0
      · subst w; simp
      · exact (((G k).metric t).pos x w hw).le
    have hnorm := ((G k).connection t).abs_ricci_quadratic_le_curvatureTensorNorm x w
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((hcurv k t ht x).trans (le_max_left B 1))
        (by positivity)) hQ)
  have hcompactRef (A : ℝ) (hA : 0 < A) : ∀ᶠ k in atTop,
      IsCompact (closure (((G k).metric (-(T / 2))).ball (p k) A)) := by
    filter_upwards [hcompact (E * A) (mul_pos hE hA)] with k hk
    apply hk.of_isClosed_subset isClosed_closure
    apply closure_mono
    have hball := (G k).ball_subset_ball_of_ricci_bound
      (convex_Icc (-T) 0) (Subset.refl _) (p k) A L href hzero
      (fun t ht x _ w => hRic k t ht x w)
    have hdisplacement : |(0 : ℝ) - -(T / 2)| ≤ T := by
      rw [zero_sub, neg_neg, abs_of_pos (half_pos hT)]
      linarith
    have hexp : Real.exp (L * |(0 : ℝ) - -(T / 2)|) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdisplacement hL)
    intro x hx
    exact (hball hx).trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hexp hA.le))
  let Cbig : ℕ → FlowCarrier.{u} 3 := fun k => {
    carrier := N k
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := inferInstance
    chartedSpace := inferInstance
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := inferInstance
    connected := isConnected_univ }
  let Csmall : ℕ → FlowCarrier.{0} 3 := fun k => (Cbig k).shrink
  have hshift : (fun t : ℝ => t + -(T / 2)) '' Ioo (-T / 2) (T / 2) ⊆
      Icc (-T) 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hne : (Ioo (-T / 2) (T / 2)).Nontrivial := by
    refine ⟨-T / 4, ⟨by linarith, by linarith⟩,
      T / 4, ⟨by linarith, by linarith⟩, by linarith⟩
  let Fsmall (k : ℕ) : RicciFlow 3 (Csmall k).carrier (Ioo (-T / 2) (T / 2)) :=
    (G k).shrink.translate (-(T / 2)) hshift ordConnected_Ioo hne
  let S : PointedFlowSequence 3 (-T / 2) (T / 2) := {
    carrier := Csmall
    flow := fun k => {
      base := equivShrink (N k) (p k)
      flow := Fsmall k
      volumeMeasure := (Csmall k).metricHausdorffVolume ((Fsmall k).metric 0)
      spacetimeVectorField := fun _ _ => (1, 0)
      spacetimeVectorField_time := fun _ _ => rfl
      spacetimeVectorField_spatial_zero := fun _ _ => rfl } }
  have hcurvSmall (k : ℕ) (t : ℝ) (ht : t ∈ Ioo (-T / 2) (T / 2))
      (x : (Csmall k).carrier) :
      ((S.flow k).flow.connection t).curvatureTensorNorm x ≤ K := by
    change ((G k).shrink.connection (t - T / 2)).curvatureTensorNorm x ≤ K
    rw [RicciFlow.shrink_curvatureTensorNorm]
    exact (hcurv k (t - T / 2) (hshift ⟨t, ht, rfl⟩) _).trans (le_max_left B 1)
  have hzeroBall (k : ℕ) (A : ℝ) :
      (S.flow k).zeroBall A = (equivShrink (N k)).symm ⁻¹'
        (((G k).metric (-(T / 2))).ball (p k) A) := by
    ext x
    change ((G k).shrink.metric (0 + -(T / 2))).edist
      (equivShrink (N k) (p k)) x < ENNReal.ofReal A ↔ _
    rw [zero_add, RicciFlow.shrink_edist, Equiv.symm_apply_apply]
    rfl
  have hnoncollapse : ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (κ * r ^ 3) ≤ (S.flow k).zeroBallVolume r := by
    let r : ℝ := E * rho
    let w : ℝ := Real.exp (-((3 : ℝ) * L * T)) * v
    let κcal : ℝ := w / r ^ 3
    let c : ℝ := (euclideanVolumeCalibration 3).toReal
    have hr : 0 < r := mul_pos hE hrho
    have hw : 0 < w := mul_pos (Real.exp_pos _) hv
    have hκcal : 0 < κcal := div_pos hw (pow_pos hr 3)
    have hc : 0 < c := ENNReal.toReal_pos (euclideanVolumeCalibration_pos 3).ne'
      (euclideanVolumeCalibration_ne_top 3)
    have hproduct : κcal * r ^ 3 = w := div_mul_cancel₀ _ (pow_ne_zero 3 hr.ne')
    refine ⟨r, κcal / c, hr, div_pos hκcal hc, ?_⟩
    filter_upwards [hvolume] with k hk
    have htransfer := terminal_ball_volume_lower_bound_at_time
      (G k) hT (p k) (hcurv k) hk
    have hvol := (htransfer (-(T / 2)) href).2
    have hsmall : ENNReal.ofReal (κcal * r ^ 3) ≤
        calibratedMetricVolume ((G k).shrink.metric (-(T / 2)))
          (((G k).shrink.metric (-(T / 2))).ball (equivShrink (N k) (p k)) r) := by
      rw [hproduct, calibratedMetricVolume_eq_volumeMeasure,
        RicciFlow.shrink_volumeMeasure_ball, Equiv.symm_apply_apply]
      exact hvol
    have hhaus := calibrated_noncollapse_to_hausdorff (Csmall k)
      ((G k).shrink.metric (-(T / 2)))
      (((G k).shrink.metric (-(T / 2))).ball (equivShrink (N k) (p k)) r)
      hκcal hr hsmall
    change ENNReal.ofReal ((κcal / c) * r ^ 3) ≤
      (Csmall k).metricHausdorffVolume ((G k).shrink.metric (0 + -(T / 2)))
        (((G k).shrink.metric (0 + -(T / 2))).ball (equivShrink (N k) (p k)) r)
    simpa only [zero_add] using hhaus
  let H : PointedRicciFlowCompactnessHypotheses 3 (-T / 2) (T / 2) := {
    time_bounds := ⟨by linarith, by linarith⟩
    sequence := S
    volume_compatibility := fun _ => rfl
    zero_time_ball_compact := by
      intro A hA
      filter_upwards [hcompactRef A hA] with k hk
      dsimp only
      rw [hzeroBall]
      let e := (Poincare.Topology.SecondCountable.homeomorphShrink (N k)).symm
      change IsCompact (closure (e ⁻¹' (((G k).metric (-(T / 2))).ball (p k) A)))
      rw [← e.preimage_closure]
      exact e.isCompact_preimage.mpr hk
    spacetime_control := by
      intro A _ I _ _ _ hI
      refine ⟨K, hK, Eventually.of_forall (fun k => ?_)⟩
      refine ⟨SmoothSpacetimeEmbedding.refl (S.flow k)
        (I ×ˢ (S.flow k).zeroBall A), fun _ _ => rfl, ?_⟩
      exact ⟨hK, fun t ht x _ => hcurvSmall k t (hI ht) x⟩
    all_time_curvature_control := by
      intro A _
      refine ⟨K, hK, Eventually.of_forall (fun k => ?_)⟩
      dsimp only
      intro _ _ t ht x _
      exact hcurvSmall k t ht x
    noncollapsing := hnoncollapse }
  refine ⟨H, ?_⟩
  intro k
  dsimp only
  refine ⟨(Poincare.Manifold.shrinkDiffeomorph (𝓡 3) (N k)).symm, ?_, ?_⟩
  · exact (equivShrink (N k)).symm_apply_apply (p k)
  · intro t x a b
    rfl

end PoincareConjecture.M30
