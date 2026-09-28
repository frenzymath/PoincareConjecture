import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.CutTime








noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.VolumeComparison



theorem exists_ray_interval_sdiff_terminal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {R : ℝ} (h0 : (0 : E) ∈ S) (hS : S ⊆ Metric.ball 0 R)
    (hstar : ∀ v ∈ S, ∀ a : ℝ, 0 ≤ a → a ≤ 1 → a • v ∈ S)
    {θ : E} (hθ : ‖θ‖ = 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ R ∧
      ∀ t : ℝ, 0 < t → (t • θ ∈ S \ terminalRadialPoints S R ↔ t < c) := by
  let A : Set ℝ := {t | 0 ≤ t ∧ t • θ ∈ S}
  have hA0 : 0 ∈ A := ⟨le_rfl, by simpa using h0⟩
  have hAR (t : ℝ) (ht : t ∈ A) : t < R := by
    have h := mem_ball_zero_iff.mp (hS ht.2)
    simpa only [norm_smul, Real.norm_of_nonneg ht.1, hθ, mul_one] using h
  have hAbdd : BddAbove A := ⟨R, fun t ht => (hAR t ht).le⟩
  refine ⟨sSup A, le_csSup hAbdd hA0,
    csSup_le ⟨0, hA0⟩ (fun t ht => (hAR t ht).le), ?_⟩
  intro t ht
  have htθ : ‖t • θ‖ = t := by
    rw [norm_smul, Real.norm_of_nonneg ht.le, hθ, mul_one]
  have htne : t • θ ≠ 0 := by
    intro h
    have := congrArg norm h
    rw [htθ, norm_zero] at this
    exact ht.ne' this
  constructor
  · intro htS
    obtain ⟨q, hq, hqR, hqS⟩ : ∃ q : ℚ, 1 < (q : ℝ) ∧
        (q : ℝ) * ‖t • θ‖ < R ∧ (q : ℝ) • (t • θ) ∈ S := by
      by_contra h
      exact htS.2 ⟨htS.1, htne, mem_iInter.mpr (fun q hq => h ⟨q, hq⟩)⟩
    have hqt : t < (q : ℝ) * t := by nlinarith
    exact hqt.trans_le (le_csSup hAbdd
      ⟨ht.le.trans hqt.le, by simpa only [smul_smul] using hqS⟩)
  · intro htc
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ htc
    have hs0 : 0 < s := ht.trans hts
    have hscale : (t / s) • (s • θ) = t • θ := by
      rw [smul_smul, div_mul_cancel₀ _ hs0.ne']
    have htS : t • θ ∈ S := hscale ▸
      hstar _ hs.2 (t / s) (div_nonneg ht.le hs0.le)
        ((div_le_one hs0).mpr hts.le)
    refine ⟨htS, ?_⟩
    intro hterm
    obtain ⟨q, hq1, hqst⟩ := exists_rat_btwn
      (show (1 : ℝ) < s / t from (lt_div_iff₀ ht).mpr (by simpa using hts))
    have hqt : (q : ℝ) * t < s := (lt_div_iff₀ ht).mp hqst
    have hq0 : 0 ≤ (q : ℝ) := by linarith
    have hqS : (q : ℝ) • (t • θ) ∈ S := by
      have h := hstar _ hs.2 ((q : ℝ) * t / s)
        (div_nonneg (mul_nonneg hq0 ht.le) hs0.le) ((div_le_one hs0).mpr hqt.le)
      simpa only [smul_smul, div_mul_cancel₀ _ hs0.ne'] using h
    exact (mem_iInter.mp hterm.2.2 q)
      ⟨hq1, by rw [htθ]; exact hqt.trans (hAR s hs), hqS⟩

end Poincare.VolumeComparison
