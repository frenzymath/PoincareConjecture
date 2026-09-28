import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.TimeSupport

set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Bundle intervalIntegral NNReal

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum ReducedLengthMinimum.Variational

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

private noncomputable def initialBackwardSubpath (K : AncientKappaSolution 2 M)
    {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ u)
    (path : BackwardTimePath K.flow 0 0 u) : BackwardTimePath K.flow 0 0 τ where
  curve := path.curve
  nonnegative := le_rfl
  ordered := hτ
  terminal_mem := path.terminal_mem
  time_mem s hs := path.time_mem s ⟨hs.1, hs.2.trans hu⟩
  continuous := path.continuous.mono (Icc_subset_Icc_right hu)
  regular := path.regular.mono (Ioo_subset_Ioo_right hu)
  l_integrable := path.l_integrable.mono_set (by
    rw [uIcc_of_le hτ.le, uIcc_of_le (hτ.le.trans hu)]
    exact Icc_subset_Icc_right hu)

theorem monotoneOn_spatial_minimum_action (K : AncientKappaSolution 2 M) (p : M) :
    MonotoneOn (fun τ => 2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ) (Ioi 0) := by
  intro τ hτ u _hu hu
  change 0 < τ at hτ
  obtain ⟨paths, α, hstart, hanti, hlim, hα0, huniform⟩ :=
    K.exists_uniformly_convergent_spatial_minimizing_paths p (hτ.trans_le hu)
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  let path := K.initialBackwardSubpath hτ hu (paths k)
  have hred := K.reducedLength_le_path path (hstart k) rfl
  have hden : 0 < 2 * Real.sqrt τ := by positivity
  have hbound := (le_div_iff₀ hden).mp
    ((K.spatialReducedLengthInfimum_le p (path.curve τ) τ).trans hred)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) u)]
      backwardLIntegrand K.flow 0 (paths k).curve := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact K.backwardLIntegrand_nonneg _ hs.1.le
  have hmono := intervalIntegral.integral_mono_interval (a := (0 : ℝ)) le_rfl hτ.le hu
    hnonneg (paths k).l_integrable
  have hpath : backwardLLength K.flow 0 0 τ path.curve ≤
      backwardLLength K.flow 0 0 u (paths k).curve := hmono
  have hbound' : 2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ ≤
      backwardLLength K.flow 0 0 τ path.curve := by
    simpa only [mul_comm] using hbound
  exact hbound'.trans hpath

theorem exists_spatial_minimum_action_increment_bound (K : AncientKappaSolution 2 M)
    (p : M) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ u : ℝ, 0 < τ → τ ≤ u → u ≤ B →
      2 * Real.sqrt u * K.spatialReducedLengthInfimum p u -
        2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ ≤ C * (u - τ) := by
  obtain ⟨L, hL, hcompare⟩ := K.exists_uniform_reducedLength_comparator p B
  obtain ⟨S, hS, hsub⟩ := K.exists_compact_reducedLength_sublevels p B L
  obtain ⟨C, hC, hcurv⟩ := K.exists_curvature_bound_on_compact hS hB
  refine ⟨Real.sqrt B * C, mul_nonneg (Real.sqrt_nonneg B) hC, ?_⟩
  intro τ u hτ hu huB
  have hu' : 0 < u := hτ.trans_le hu
  obtain ⟨q, hq, hsupport⟩ := K.exists_stationary_time_comparison p hτ
  have hqS : q ∈ S := hsub τ hτ (hu.trans huB) (by
    change reducedLength K.flow 0 p q τ ≤ L
    rw [hq]
    exact (K.spatialReducedLengthInfimum_le p p τ).trans (hcompare τ hτ (hu.trans huB)))
  have hR (r : ℝ) (hr : r ∈ Icc τ u) :
      (K.flow.connection (0 - r)).scalarCurvature q ≤ C := by
    have htime : 0 - r ∈ Icc (-B) 0 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h := hcurv (0 - r) htime q hqS
    rw [(K.flow.connection (0 - r)).curvatureTensorNorm_eq_abs_scalarCurvature q,
      abs_abs] at h
    exact (le_abs_self _).trans h
  have hcont : ContinuousOn
      (fun r => Real.sqrt r * (K.flow.connection (0 - r)).scalarCurvature q) (Icc τ u) :=
    Real.continuous_sqrt.continuousOn.mul
      ((K.flow.continuousOn_scalarCurvature_ancient_surface q).comp
        (continuous_const.sub continuous_id).continuousOn
        (fun r hr => show 0 - r ∈ Iic 0 from by
          exact sub_nonpos.mpr (hτ.le.trans hr.1)))
  have htail : (∫ r in τ..u,
      Real.sqrt r * (K.flow.connection (0 - r)).scalarCurvature q) ≤
        (u - τ) * (Real.sqrt B * C) := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hu (hcont.intervalIntegrable_of_Icc hu)
      intervalIntegrable_const (fun r hr =>
        (mul_le_mul_of_nonneg_left (hR r hr) (Real.sqrt_nonneg r)).trans
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hr.2.trans huB)) hC))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have hden : 0 < 2 * Real.sqrt u := by positivity
  have hact := (le_div_iff₀ hden).mp (hsupport u hu)
  nlinarith

theorem exists_lipschitzOn_spatial_minimum_action (K : AncientKappaSolution 2 M)
    (p : M) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun τ => 2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ) (Ioc 0 B) := by
  obtain ⟨C, hC, hbound⟩ := K.exists_spatial_minimum_action_increment_bound p hB
  refine ⟨⟨C, hC⟩, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro τ hτ u hu
  change |2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ -
      2 * Real.sqrt u * K.spatialReducedLengthInfimum p u| ≤ C * |τ - u|
  rcases le_total τ u with htu | hut
  · have hmono := K.monotoneOn_spatial_minimum_action p hτ.1 hu.1 htu
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr htu)]
    nlinarith [hbound τ u hτ.1 htu hu.2]
  · have hmono := K.monotoneOn_spatial_minimum_action p hu.1 hτ.1 hut
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hut)]
    exact hbound u τ hu.1 hut hτ.2

theorem continuousOn_spatialReducedLengthInfimum (K : AncientKappaSolution 2 M)
    (p : M) : ContinuousOn (K.spatialReducedLengthInfimum p) (Ioi 0) := by
  have haction : ContinuousOn
      (fun τ => 2 * Real.sqrt τ * K.spatialReducedLengthInfimum p τ) (Ioi 0) := by
    intro τ hτ
    change 0 < τ at hτ
    obtain ⟨C, hC⟩ := K.exists_lipschitzOn_spatial_minimum_action p (by linarith : 0 < τ + 1)
    exact (hC.continuousOn.continuousAt
      (Ioc_mem_nhds hτ (by linarith : τ < τ + 1))).continuousWithinAt
  have hquot := haction.div (continuous_const.mul Real.continuous_sqrt).continuousOn
    (fun τ hτ => show 2 * Real.sqrt τ ≠ 0 by
      change 0 < τ at hτ
      positivity)
  apply hquot.congr
  intro τ hτ
  change 0 < τ at hτ
  exact (mul_div_cancel_left₀ (K.spatialReducedLengthInfimum p τ)
    (show 2 * Real.sqrt τ ≠ 0 by positivity)).symm

end PoincareConjecture.AncientKappaSolution
