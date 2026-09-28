import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_AdjustedComparison
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

theorem exists_initial_exact_comparison_threshold
    (g₀ : StandardInitialMetric) {tolerance : ℝ} (htol : 0 < tolerance) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (S : GeneralizedSliceCarrier.{u})
      (g : RiemannianMetric 3 S.carrier) (tip : S.carrier) (scale eta : ℝ),
      SurgeryCapClose g₀ S g tip scale eta → eta ≤ delta →
        ∃ Q' : SurgeryCapClose g₀ S g tip scale tolerance,
          ∀ r : ℝ, 0 < r → r ≤ tolerance⁻¹ →
            Q'.map '' g₀.metric.ball 0 r = g.ball tip (scale * r) := by
  classical
  by_contra! hbad
  let R : ℝ := 4 * tolerance⁻¹
  have hR : 0 < R := mul_pos (by norm_num) (inv_pos.mpr htol)
  obtain ⟨delta, hdelta, hexp⟩ := exists_initial_exponential_threshold.{u} R hR
  have hseq (n : ℕ) := hbad (min delta (1 / ((n : ℝ) + 1)))
    (lt_min hdelta (by positivity))
  choose S g tip scale eta Q heta hfail using hseq
  have he : Tendsto eta atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (Q n).eta_pos.le)
      (fun n => (heta n).trans (min_le_right _ _))
  have hD (n : ℕ) : Nonempty (NormalizedCapExponential (Q n) R) :=
    hexp g₀ (S n) (g n) (tip n) (scale n) (eta n) (Q n)
      ((heta n).trans (min_le_left _ _))
  let D (n : ℕ) : NormalizedCapExponential (Q n) R := Classical.choice (hD n)
  obtain ⟨φ, hφ, L, hL, hLinner⟩ := exists_subseq_initial_exponential_frames
    g₀ S g tip scale eta (fun _ => R) Q D he
  have hfit : tolerance⁻¹ < R / 2 := by
    dsimp [R]
    linarith [inv_pos.mpr htol]
  have hadjust := eventually_adjusted_comparisons g₀ (S ∘ φ)
    (fun n => g (φ n)) (fun n => tip (φ n)) (scale ∘ φ) (eta ∘ φ)
    (fun n => Q (φ n)) (fun n => D (φ n))
    (he.comp hφ.tendsto_atTop) L hL hLinner htol hfit
  obtain ⟨n, Q', _, hballs⟩ := hadjust.exists
  obtain ⟨r, hr, hrt, hne⟩ := hfail (φ n) Q'
  exact hne (hballs r hr hrt)

end PoincareConjecture.M44
