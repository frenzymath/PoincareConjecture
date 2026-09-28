import PoincareConjecture.Proofs.M35.TerminalBlowup.RadialWarping
import PoincareConjecture.Proofs.M35.TerminalBlowup.Mathlib.WeightedRadius
import PoincareConjecture.Proofs.M35.TerminalBlowup.EndScalarFloor
import PoincareConjecture.Proofs.M35.TerminalBlowup.MetricNondegeneration











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1



theorem radialArclength_tendsto_atTop
    (g : RiemannianMetric 3 StandardCapSpace) (hcomplete : MetricComplete g) :
    Tendsto (radialArclength g) atTop atTop := by
  apply tendsto_atTop.2
  intro R
  obtain ⟨r, _, hR⟩ := radialArclength_unbounded g hcomplete R
  exact (eventually_ge_atTop r).mono
    (fun u hu => hR.le.trans ((radialArclength_strictMono g).monotone hu))



theorem axisWarpingRadius_sq_le_of_exterior_scalar_floor
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {c : ℝ} (hc : 0 < c) {K : Set StandardCapSpace} (hK : IsCompact K)
    (hfloor : ∀ x, x ∉ K → c ≤ D.scalarCurvature x)
    {r : ℝ} (hr : 0 < r) : axisWarpingRadius g r ^ 2 ≤ 2 / c := by
  have hconcave (u : ℝ) (hu : 0 < u) : axisWarpingSecond g u ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (axisWarpingRadius_pos g hu).le)
        (radialMixedCurvatureFactor_nonneg D hrotation hsec hu)
    · exact (axisRadialCoefficient_pos g u).le
  have hscalar (u : ℝ) (hu : 0 < u) : D.scalarCurvature (u • e 2) =
      2 * (1 - axisWarpingSlope g u ^ 2) / axisWarpingRadius g u ^ 2 -
        4 * axisWarpingSecond g u / axisWarpingRadius g u := by
    rw [rotational_scalar_axis D hrotation hu]
    calc
      _ = 2 * (radialTangentialCurvatureFactor g u / axisAngularCoefficient g u) +
          4 * (radialMixedCurvatureFactor g u / axisRadialCoefficient g u) := by ring
      _ = _ := by
        rw [radialTangentialCurvatureFactor_eq_warping g hu,
          radialMixedCurvatureFactor_eq_warping g hu]
        ring
  have hend : ∀ᶠ u in atTop,
      c ≤ 2 * (1 - axisWarpingSlope g u ^ 2) / axisWarpingRadius g u ^ 2 -
        4 * axisWarpingSecond g u / axisWarpingRadius g u := by
    obtain ⟨B, hB, hbound⟩ := hK.isBounded.exists_pos_norm_le
    filter_upwards [eventually_gt_atTop B] with u hu
    have hu0 : 0 < u := hB.trans hu
    rw [← hscalar u hu0]
    apply hfloor
    intro hmem
    have hh := hbound (u • e 2) hmem
    have heq : ‖u • e 2‖ = u := by
      simp [e, norm_smul, Real.norm_eq_abs, abs_of_pos hu0]
    rw [heq] at hh
    exact not_le_of_gt hu hh
  exact weighted_radial_radius_sq_le_of_eventual_scalar_floor
    (fun u hu => axisWarpingRadius_pos g hu)
    (fun u hu => axisWarpingRadius_hasDerivAt g hu)
    (fun u hu => axisWarpingSlope_hasDerivAt g hu)
    (fun u _ => radialArclength_hasDerivAt g u)
    (fun u _ => axisRadialSpeed_pos g u)
    (radialArclength_tendsto_atTop g hcomplete) hconcave hc hend hr

end PoincareConjecture.M35.Uniqueness

namespace PoincareConjecture.RepairedStandardCapExistenceData

open M35.Uniqueness



theorem axisWarpingRadius_sq_le_remaining_time
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {t r : ℝ}
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (hr : 0 < r) :
    axisWarpingRadius (E.flow.metric t) r ^ 2 ≤ 4 * (1 - t) := by
  obtain ⟨K, hK, hfloor⟩ := E.exists_compact_exterior_terminal_scalar_floor P ht
  have htone : t < 1 := E.lifetime_one ▸ ht.2
  have hc : 0 < 1 / (2 * (1 - t)) := by positivity
  have h := axisWarpingRadius_sq_le_of_exterior_scalar_floor (E.flow.connection t)
    (E.rotation_invariant t ht) (E.complete t ht) (E.nonnegative_sectional t ht)
    hc hK (fun x hx => (hfloor x hx).le) hr
  convert h using 1
  field_simp
  ring



theorem angular_tangent_inner_le_remaining_time
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {t : ℝ}
    (ht : t ∈ Ico 0 E.flow.base.lifetime) {x : StandardCapSpace} (hx : x ≠ 0)
    (v : StandardCapSpace) (hv : inner ℝ x v = 0) :
    (E.flow.metric t).inner x v v ≤ 4 * (1 - t) * (‖v‖ ^ 2 / ‖x‖ ^ 2) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hrad := E.axisWarpingRadius_sq_le_remaining_time P ht hr
  have hrad' : ‖x‖ ^ 2 * axisAngularCoefficient (E.flow.metric t) ‖x‖ ≤
      4 * (1 - t) := by
    simpa only [axisWarpingRadius, mul_pow,
      Real.sq_sqrt (axisAngularCoefficient_pos (E.flow.metric t) ‖x‖).le] using hrad
  rw [rotational_metric_form_correction (E.flow.metric t) (E.rotation_invariant t ht) hx,
    hv, mul_zero, add_zero, real_inner_self_eq_norm_sq]
  calc
    _ = (‖x‖ ^ 2 * axisAngularCoefficient (E.flow.metric t) ‖x‖) *
        (‖v‖ ^ 2 / ‖x‖ ^ 2) := by field_simp [hr.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hrad' (div_nonneg (sq_nonneg _) (sq_nonneg _))



theorem angular_tangent_metric_tendsto_zero
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {x : StandardCapSpace} (hx : x ≠ 0)
    (v : StandardCapSpace) (hv : v ≠ 0) (horth : inner ℝ x v = 0) :
    Tendsto (fun t => (E.flow.metric t).inner x v v) (𝓝[<] 1) (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun t => ((E.flow.metric t).pos x v hv).le))
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with t ht htpos
    exact E.angular_tangent_inner_le_remaining_time P
      ⟨htpos.le, E.lifetime_one.symm ▸ ht⟩ hx v horth
  · have hcont : Continuous (fun t : ℝ => 4 * (1 - t) * (‖v‖ ^ 2 / ‖x‖ ^ 2)) := by
      fun_prop
    simpa only [sub_self, mul_zero, zero_mul] using
      (hcont.continuousAt (x := 1)).tendsto.mono_left nhdsWithin_le_nhds

private theorem exists_nonzero_angular_vector (x : StandardCapSpace) :
    ∃ v : StandardCapSpace, v ≠ 0 ∧ inner ℝ x v = 0 := by
  let e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1
  by_cases hx : x 0 = 0
  · refine ⟨e 0, ?_, ?_⟩
    · intro heq
      have h := congrArg (fun v : StandardCapSpace => v 0) heq
      simp [e] at h
    · simp [e, EuclideanSpace.inner_single_right, hx]
  · refine ⟨(-x 1) • e 0 + x 0 • e 1, ?_, ?_⟩
    · intro heq
      have h := congrArg (fun v : StandardCapSpace => v 1) heq
      apply hx
      simpa [e] using h
    · simp [e, inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right]
      ring



theorem scalar_tendsto_off_origin
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {x : StandardCapSpace} (hx : x ≠ 0) :
    Tendsto (fun t => (E.flow.connection t).scalarCurvature x) (𝓝[<] 1) atTop := by
  obtain ⟨v, hv, horth⟩ := exists_nonzero_angular_vector x
  exact E.scalar_tendsto_of_tangent_metric_tendsto_zero P x v hv
    (E.angular_tangent_metric_tendsto_zero P hx v hv horth)

end PoincareConjecture.RepairedStandardCapExistenceData
