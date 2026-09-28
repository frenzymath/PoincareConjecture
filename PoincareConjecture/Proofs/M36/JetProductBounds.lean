import PoincareConjecture.Proofs.M36.CylinderTwoJet
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped ContDiff BigOperators

namespace PoincareConjecture.M36

open PoincareConjecture.SpacetimeBounds

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem norm_metricTwoJet_le_iff {F : E₃ → MetricCoefficient 3} {x : E₃} {B : ℝ} :
    ‖metricTwoJet F x‖ ≤ B ↔
      ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k F x‖ ≤ B := by
  simp only [metricTwoJet, Prod.norm_def, max_le_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩ k hk
    interval_cases k
    · simpa only [norm_iteratedFDeriv_zero] using h0
    · simpa only [norm_iteratedFDeriv_one] using h1
    · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
      exact h2
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [norm_iteratedFDeriv_zero] using h 0 (by omega)
    · simpa only [norm_iteratedFDeriv_one] using h 1 (by omega)
    · have h2 := h 2 (by omega)
      rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h2

theorem norm_metricTwoJet_smul_le
    {f : E₃ → ℝ} {G : E₃ → MetricCoefficient 3} {x : E₃}
    (hf : ContDiffAt ℝ ∞ f x) (hG : ContDiffAt ℝ ∞ G x)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfjet : ∀ k : ℕ, k ≤ 2 → ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hGjet : ‖metricTwoJet G x‖ ≤ B) :
    ‖metricTwoJet (fun p => f p • G p) x‖ ≤ 4 * A * B := by
  apply norm_metricTwoJet_le_iff.mpr
  intro k hk
  have hGj := norm_metricTwoJet_le_iff.mp hGjet
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) G x‖ :=
      Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt hf hG k
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfjet i (hik.trans hk)) (Nat.cast_nonneg _))
        (hGj (k - i) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ ≤ 4 * A * B := by
      interval_cases k <;> norm_num [Finset.sum_range_succ] <;>
        nlinarith only [mul_nonneg hA hB]

theorem metricTwoJet_const_smul (c : ℝ) {G : E₃ → MetricCoefficient 3} {x : E₃}
    (hG : ContDiffAt ℝ ∞ G x) :
    metricTwoJet (fun p => c • G p) x = c • metricTwoJet G x := by
  have hfirst : fderiv ℝ (fun p => c • G p) =ᶠ[nhds x] fun p => c • fderiv ℝ G p := by
    filter_upwards [(hG.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)]
      with p hp
    exact fderiv_const_smul (hp.differentiableAt (by simp)) c
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact fderiv_const_smul (hG.differentiableAt (by simp)) c
  change fderiv ℝ (fderiv ℝ (fun p => c • G p)) x = c • fderiv ℝ (fderiv ℝ G) x
  rw [hfirst.fderiv_eq]
  exact fderiv_const_smul
    ((hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)) c

end PoincareConjecture.M36
