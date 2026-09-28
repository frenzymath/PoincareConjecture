import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedCoefficients
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem exists_initial_comparison_domain_threshold (g₀ : StandardInitialMetric)
    {K : Set E} (hK : IsCompact K) (j : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ eta : ℝ, 0 < eta → eta ≤ delta →
      j ≤ ⌊eta⁻¹⌋₊ ∧ K ⊆ g₀.metric.ball 0 eta⁻¹ := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (((M36.radialArclength_contDiff g₀).continuous.comp continuous_norm).continuousOn)
  have hden : 0 < |B| + (j : ℝ) + 1 := by positivity
  refine ⟨(|B| + (j : ℝ) + 1)⁻¹, inv_pos.mpr hden, ?_⟩
  intro eta heta hsmall
  have hinv := one_div_le_one_div_of_le heta hsmall
  simp only [one_div, inv_inv] at hinv
  refine ⟨(Nat.le_floor_iff (inv_pos.mpr heta).le).mpr (by linarith [abs_nonneg B]), ?_⟩
  intro x hx
  change g₀.metric.edist 0 x < ENNReal.ofReal eta⁻¹
  rw [M36.standard_edist_zero, ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr heta)]
  have hb : M36.radialArclength g₀ ‖x‖ ≤ |B| :=
    (le_abs_self _).trans ((hB x hx).trans (le_abs_self B))
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem tendstoUniformlyOn_initial_coefficient_jets
    (g₀ : StandardInitialMetric)
    (S : ℕ → GeneralizedSliceCarrier.{u})
    (g : (n : ℕ) → RiemannianMetric 3 (S n).carrier)
    (tip : (n : ℕ) → (S n).carrier) (scale eta : ℕ → ℝ)
    (Q : (n : ℕ) → SurgeryCapClose g₀ (S n) (g n) (tip n) (scale n) (eta n))
    (heta : Tendsto eta atTop (𝓝 0))
    (j : ℕ) {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => iteratedFDeriv ℝ j (Q n).normalizedCoefficients)
      (iteratedFDeriv ℝ j g₀.metric.euclideanCoefficients) atTop K := by
  obtain ⟨C, hC, hbound⟩ := SurgeryCapClose.exists_normalized_coefficient_jet_bound
    g₀ hK j
  obtain ⟨delta, hdelta, hdomain⟩ := exists_initial_comparison_domain_threshold g₀ hK j
  have hfit : ∀ᶠ n in atTop, j ≤ ⌊(eta n)⁻¹⌋₊ ∧ K ⊆ g₀.metric.ball 0 (eta n)⁻¹ := by
    filter_upwards [heta.eventually (gt_mem_nhds hdelta)] with n hn
    exact hdomain (eta n) (Q n).eta_pos hn.le
  have herror : Tendsto (fun n => C * eta n) atTop (𝓝 0) := by
    simpa only [mul_zero] using heta.const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  filter_upwards [hfit, herror.eventually (gt_mem_nhds hepsilon)] with n hn herr
  intro x hx
  have hB : ContDiffAt ℝ ∞ (Q n).normalizedCoefficients x :=
    (Q n).contDiffOn_normalizedCoefficients.contDiffAt
      ((Q n).toPartialDiffeomorph.open_source.mem_nhds (hn.2 hx))
  have hg := g₀.metric.contDiffAt_euclideanCoefficients x
  have hb := hbound (S n) (g n) (tip n) (scale n) (eta n) (Q n) hn.1 hn.2 x hx
  rw [iteratedFDeriv_sub_apply
    (hB.of_le (by exact_mod_cast le_top)) (hg.of_le (by exact_mod_cast le_top))] at hb
  simpa only [dist_eq_norm, norm_sub_rev] using hb.trans_lt herr

end PoincareConjecture.M44
