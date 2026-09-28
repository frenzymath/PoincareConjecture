import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.ScalarComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.CutTime

noncomputable section
set_option autoImplicit false

open Set
open scoped ENNReal

namespace Poincare.VolumeComparison

theorem smul_mem_sdiff_terminalRadialPoints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {R : ℝ}
    (hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S)
    {v : E} (hv : v ∈ S \ terminalRadialPoints S R)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    a • v ∈ S \ terminalRadialPoints S R := by
  refine ⟨hstar v hv.1 a ha0.le ha1, ?_⟩
  intro hterm
  by_cases hv0 : v = 0
  · exact hterm.2.1 (by simp [hv0])
  obtain ⟨q, hq, hqR, hqS⟩ : ∃ q : ℚ, 1 < (q : ℝ) ∧ (q : ℝ) * ‖v‖ < R ∧
      (q : ℝ) • v ∈ S := by
    by_contra h
    exact hv.2 ⟨hv.1, hv0, mem_iInter.mpr (fun q hq => h ⟨q, hq⟩)⟩
  have hqa : (q : ℝ) * ‖a • v‖ < R := by
    rw [norm_smul, Real.norm_of_nonneg ha0.le]
    have hq0 : 0 ≤ (q : ℝ) := by linarith
    calc
      (q : ℝ) * (a * ‖v‖) ≤ (q : ℝ) * (1 * ‖v‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha1 (norm_nonneg v)) hq0
      _ < R := by simpa only [one_mul] using hqR
  have hqav : (q : ℝ) • (a • v) ∈ S := by
    simpa only [smul_smul, mul_comm] using hstar _ hqS a ha0.le ha1
  exact (mem_iInter.mp hterm.2.2 q) ⟨hq, hqa, hqav⟩

theorem indicator_cross_le {F G : ℝ → ℝ≥0∞} {S : Set ℝ} {R : ℝ}
    (hdown : ∀ t ∈ Ioo (0 : ℝ) R, ∀ s ∈ Ioo (0 : ℝ) R,
      t ≤ s → s ∈ S → t ∈ S)
    (hcross : ∀ t ∈ Ioo (0 : ℝ) R, ∀ s ∈ Ioo (0 : ℝ) R,
      t ≤ s → t ∈ S → s ∈ S → F s * G t ≤ F t * G s)
    {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) R) (hs : s ∈ Ioo (0 : ℝ) R) (hts : t ≤ s) :
    S.indicator F s * G t ≤ S.indicator F t * G s := by
  classical
  by_cases hsS : s ∈ S
  · have htS := hdown t ht s hs hts hsS
    simpa only [indicator_of_mem hsS, indicator_of_mem htS] using
      hcross t ht s hs hts htS hsS
  · simp only [indicator_of_notMem hsS, zero_mul, zero_le]

end Poincare.VolumeComparison
