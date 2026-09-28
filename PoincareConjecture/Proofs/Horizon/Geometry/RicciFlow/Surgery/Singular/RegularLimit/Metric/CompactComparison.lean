import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_compact_uniform_curvature_tail
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) :
    ∃ s K : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 < K ∧
      ∀ t ∈ Ico s T, ∀ x ∈ A,
        (H.reference.flow.connection t).curvatureTensorNorm x ≤ K := by
  obtain ⟨B, hB⟩ := hA.bddAbove_image
    (H.terminalConnection P04).continuous_scalarCurvature.continuousOn
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) 1 zero_lt_one
  obtain ⟨a, haT, hclose⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hclose
  obtain ⟨s, hs, hsT⟩ := exists_between (max_lt haT H.reference.tMinus_lt)
  have hsref := (le_max_right a H.reference.tMinus).trans_lt hs
  refine ⟨s, 13 * max (B + 1) (Real.exp 4), hsref, hsT, by positivity, ?_⟩
  intro t ht x hx
  apply H.reference_curvature_norm_le_of_scalar_le P04 ⟨hsref.le.trans ht.1, ht.2⟩
  have hdist := hclose ⟨(le_max_left a H.reference.tMinus).trans_lt (hs.trans_le ht.1),
    ht.2⟩ x hx
  have hupper := hB ⟨x, hx, rfl⟩
  rw [Real.dist_eq] at hdist
  have := (abs_sub_lt_iff.mp hdist).2
  linarith

theorem exists_compact_terminal_metric_exponential_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) :
    ∃ s K : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 < K ∧
      ∀ t ∈ Ico s T, ∀ x ∈ A, ∀ v : TangentSpace (𝓡 3) x,
        (H.terminalMetric P04).inner x v v ≤
          Real.exp (6 * K * (T - t)) * ((H.terminalFlow P04).metric t).inner x v v ∧
        ((H.terminalFlow P04).metric t).inner x v v ≤
          Real.exp (6 * K * (T - t)) * (H.terminalMetric P04).inner x v v := by
  obtain ⟨s, K, hsref, hsT, hK, hbound⟩ := H.exists_compact_uniform_curvature_tail P04 hA
  refine ⟨s, K, hsref, hsT, hK, ?_⟩
  intro t ht x hx v
  have hb := H.terminalMetricBilinear_bounds P04 x.property
    (hsref.le.trans ht.1) ht.2 hK.le
    (fun u hu => hbound u ⟨ht.1.trans hu.1, hu.2⟩ x hx) v
  have hold : ((H.terminalFlow P04).metric t).inner x v v =
      (H.reference.flow.metric t).inner (x : M) v v :=
    H.terminalMetricFamily_inner_of_ne P04 ht.2.ne x v v
  rw [hold, H.terminalMetric_inner]
  constructor
  · simpa only [show 2 * (3 : ℝ) = 6 by norm_num] using hb.2
  · have hmul := mul_le_mul_of_nonneg_left hb.1 (Real.exp_pos (6 * K * (T - t))).le
    have hexp : Real.exp (6 * K * (T - t)) * Real.exp (-2 * (3 : ℝ) * K * (T - t)) = 1 := by
      rw [← Real.exp_add]
      have he : 6 * K * (T - t) + -2 * (3 : ℝ) * K * (T - t) = 0 := by ring
      rw [he, Real.exp_zero]
    simpa only [← mul_assoc, hexp, one_mul] using hmul

theorem eventually_terminal_tangentNorm_comparison
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ t in 𝓝[<] T, ∀ x ∈ A, ∀ v : TangentSpace (𝓡 3) x,
      (H.terminalMetric P04).tangentNorm x v ≤
        c * ((H.terminalFlow P04).metric t).tangentNorm x v ∧
      ((H.terminalFlow P04).metric t).tangentNorm x v ≤
        c * (H.terminalMetric P04).tangentNorm x v := by
  obtain ⟨s, K, _, hsT, _, hbound⟩ :=
    H.exists_compact_terminal_metric_exponential_comparison P04 hA
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hexp : Tendsto (fun t : ℝ => Real.exp (6 * K * (T - t))) (𝓝[<] T) (𝓝 1) := by
    have hd : Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝 (T - T)) :=
      tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa only [Function.comp_def, sub_self, mul_zero, Real.exp_zero] using
      (Real.continuous_exp.tendsto (6 * K * (T - T))).comp (hd.const_mul (6 * K))
  have hsmall := hexp.eventually_lt_const (show 1 < c ^ 2 by nlinarith)
  filter_upwards [Ico_mem_nhdsLT hsT, hsmall] with t ht hc' x hx v
  obtain ⟨h1, h2⟩ := hbound t ht x hx v
  have hg : 0 ≤ ((H.terminalFlow P04).metric t).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (((H.terminalFlow P04).metric t).pos x v hv).le
  have hTg : 0 ≤ (H.terminalMetric P04).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((H.terminalMetric P04).pos x v hv).le
  have hsqrt (a b : ℝ) (hb : 0 ≤ b) (hab : a ≤ Real.exp (6 * K * (T - t)) * b) :
      Real.sqrt a ≤ c * Real.sqrt b := by
    have hh := Real.sqrt_le_sqrt (hab.trans (mul_le_mul_of_nonneg_right hc'.le hb))
    rwa [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hcpos.le] at hh
  exact ⟨hsqrt _ _ hg h1, hsqrt _ _ hTg h2⟩

end PoincareConjecture.SingularTimeAssumptions
