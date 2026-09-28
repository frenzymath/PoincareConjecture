import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CompactnessFeedBirthExtension
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_TwoJetModulus
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace
local notation "V" => MetricCoefficient 3

noncomputable local instance rescaledLimitEquationCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rescaledLimitEquationCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance rescaledLimitEquationTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) :=
  Prod.normedAddCommGroup

noncomputable local instance rescaledLimitEquationTwoJetSpace : NormedSpace ℝ (MetricTwoJet 3) :=
  Prod.normedSpace

theorem tendsto_metricTwoJet_of_spatialJets
    {fseq : ℕ → E → V} {f : E → V} {x : E}
    (h : ∀ m : ℕ, m ≤ 2 → Tendsto
      (fun k => iteratedFDeriv ℝ m (fseq k) x) atTop
      (𝓝 (iteratedFDeriv ℝ m f x))) :
    Tendsto (fun k => metricTwoJet (fseq k) x) atTop
      (𝓝 (metricTwoJet f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  have hj (m : ℕ) (hm : m ≤ 2) := Metric.tendsto_nhds.mp
    (h m hm) (eta / 2) (half_pos heta)
  filter_upwards [hj 0 (by omega), hj 1 (by omega), hj 2 le_rfl] with k h0 h1 h2
  simp only [dist_eq_norm] at h0 h1 h2 ⊢
  apply (norm_metricTwoJet_sub_le _ _ x ?_).trans_lt (half_lt_self heta)
  intro m hm
  interval_cases m
  · exact h0.le
  · exact h1.le
  · exact h2.le

theorem tendsto_metricTwoJet_of_compactSmooth
    {fseq : ℕ → ℝ × E → V} {f : ℝ × E → V} {U : Set (ℝ × E)}
    (h : CompactSmoothConvergenceOn fseq f atTop U)
    {p : ℝ × E} (hp : p ∈ U) :
    Tendsto (fun k => metricTwoJet (fun x => fseq k (p.1, x)) p.2) atTop
      (𝓝 (metricTwoJet (fun x => f (p.1, x)) p.2)) :=
  tendsto_metricTwoJet_of_spatialJets (fun m _ => tendsto_spatialJet_of_compactSmooth h hp m)

theorem rescaled_limit_coefficients_symmetric
    {fseq : ℕ → ℝ × E → V} {f : ℝ × E → V} {U : Set (ℝ × E)}
    (h : CompactSmoothConvergenceOn fseq f atTop U)
    (hsymm : ∀ p ∈ U, ∀ᶠ k in atTop, ∀ v w, fseq k p v w = fseq k p w v)
    {p : ℝ × E} (hp : p ∈ U) (v w : E) : f p v w = f p w v := by
  have hpoint := (h.uniformlyOn isCompact_singleton (singleton_subset_iff.mpr hp)).tendsto_at
    (mem_singleton p)
  have heval (u z : E) : Continuous (fun A : V => A u z) := by fun_prop
  have hleft := (heval v w).continuousAt.tendsto.comp hpoint
  have hright := (heval w v).continuousAt.tendsto.comp hpoint
  apply tendsto_nhds_unique hleft
  exact hright.congr' ((hsymm p hp).mono fun k hk => hk w v)

theorem rescaled_limit_coefficients_elliptic
    {fseq : ℕ → ℝ × E → V} {f : ℝ × E → V} {U : Set (ℝ × E)}
    (h : CompactSmoothConvergenceOn fseq f atTop U)
    {p : ℝ × E} (hp : p ∈ U) {a : ℝ}
    (hell : ∀ᶠ k in atTop, ∀ v : E, a * ‖v‖ ^ 2 ≤ fseq k p v v)
    (v : E) : a * ‖v‖ ^ 2 ≤ f p v v := by
  have hpoint := (h.uniformlyOn isCompact_singleton (singleton_subset_iff.mpr hp)).tendsto_at
    (mem_singleton p)
  have heval : Continuous (fun A : V => A v v) := by fun_prop
  exact ge_of_tendsto (heval.continuousAt.tendsto.comp hpoint)
    (hell.mono fun k hk => hk v)

theorem rescaled_limit_coefficients_positive
    {fseq : ℕ → ℝ × E → V} {f : ℝ × E → V} {U : Set (ℝ × E)}
    (h : CompactSmoothConvergenceOn fseq f atTop U)
    {p : ℝ × E} (hp : p ∈ U) {a : ℝ} (ha : 0 < a)
    (hell : ∀ᶠ k in atTop, ∀ v : E, a * ‖v‖ ^ 2 ≤ fseq k p v v)
    (v : E) (hv : v ≠ 0) : 0 < f p v v :=
  (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le
    (rescaled_limit_coefficients_elliptic h hp hell v)

theorem hasDerivAt_rescaled_limit_ricci_coefficients
    {fseq : ℕ → ℝ × E → V} {f : ℝ × E → V} {U : Set (ℝ × E)}
    (h : CompactSmoothConvergenceOn fseq f atTop U)
    (hinv : ∀ p ∈ U, (f p).IsInvertible)
    (hevol : ∀ p ∈ U, ∀ᶠ k in atTop,
      HasDerivAt (fun t => fseq k (t, p.2))
        (ricciFlowOperator 3 (metricTwoJet (fun x => fseq k (p.1, x)) p.2)) p.1)
    {p : ℝ × E} (hp : p ∈ U) :
    HasDerivAt (fun t => f (t, p.2))
      (ricciFlowOperator 3 (metricTwoJet (fun x => f (p.1, x)) p.2)) p.1 := by
  have hmodel := (h.smooth.contDiffAt (h.isOpen.mem_nhds hp)).differentiableAt (by simp)
  have htime : HasDerivAt (fun t => (t, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hmodel_time : HasDerivAt (fun t => f (t, p.2))
      (fderiv ℝ f p (1, 0)) p.1 := hmodel.hasFDerivAt.comp_hasDerivAt p.1 htime
  have hfirst := (h.fderiv.uniformlyOn isCompact_singleton
    (singleton_subset_iff.mpr hp)).tendsto_at (mem_singleton p)
  have heval : Continuous (fun A : (ℝ × E) →L[ℝ] V => A (1, 0)) := by fun_prop
  have htime_limit : Tendsto (fun k => fderiv ℝ (fseq k) p (1, 0)) atTop
      (𝓝 (fderiv ℝ f p (1, 0))) := heval.continuousAt.tendsto.comp hfirst
  have hjet := tendsto_metricTwoJet_of_compactSmooth h hp
  have hricci := ((contDiffOn_ricciFlowOperator 3).contDiffAt
    ((isOpen_ricciFlowOperator_domain 3).mem_nhds (hinv p hp))).continuousAt.tendsto.comp hjet
  have heq : ∀ᶠ k in atTop,
      fderiv ℝ (fseq k) p (1, 0) =
        ricciFlowOperator 3 (metricTwoJet (fun x => fseq k (p.1, x)) p.2) := by
    filter_upwards [h.eventually_smooth {p} isCompact_singleton
      (singleton_subset_iff.mpr hp), hevol p hp] with k hk hke
    have hkdiff := (hk p (mem_singleton p)).differentiableAt (by simp)
    have hk_time := hkdiff.hasFDerivAt.comp_hasDerivAt p.1 htime
    exact hk_time.unique hke
  have hop : fderiv ℝ f p (1, 0) =
      ricciFlowOperator 3 (metricTwoJet (fun x => f (p.1, x)) p.2) :=
    tendsto_nhds_unique htime_limit (hricci.congr' (heq.mono fun _ hk => hk.symm))
  exact hmodel_time.congr_deriv hop

end PoincareConjecture.M44
