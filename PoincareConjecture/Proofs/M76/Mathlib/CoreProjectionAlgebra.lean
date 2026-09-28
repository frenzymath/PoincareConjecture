import PoincareConjecture.Proofs.M76.Mathlib.SimplexCoreBox

set_option autoImplicit false

namespace StdSimplexCore

variable {ι : Type*} [DecidableEq ι]

noncomputable def residualMass (s : Finset ι) (η : ℝ) (q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (q i - η)

noncomputable def projectToFace (s : Finset ι) (η : ℝ) (q : ι → ℝ) : ι → ℝ :=
  fun i => if i ∈ s then
    η + (q i - η) * (1 - (s.card : ℝ) * η) / residualMass s η q else 0

theorem sum_projectToFace (s : Finset ι) (η : ℝ) (q : ι → ℝ)
    (hm : residualMass s η q ≠ 0) : ∑ i ∈ s, projectToFace s η q i = 1 := by
  have he : (∑ i ∈ s, projectToFace s η q i) =
      ∑ i ∈ s, (η + (q i - η) * (1 - (s.card : ℝ) * η) / residualMass s η q) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [projectToFace, if_pos hi]
  rw [he, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  change (∑ _i ∈ s, η) + residualMass s η q * (1 - (s.card : ℝ) * η) /
    residualMass s η q = 1
  rw [mul_div_cancel_left₀ _ hm]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem projectToFace_eq_self (s : Finset ι) (η : ℝ) (q : ι → ℝ)
    (hsum : ∑ i ∈ s, q i = 1) (hsupport : ∀ i ∉ s, q i = 0)
    (hden : 1 - (s.card : ℝ) * η ≠ 0) : projectToFace s η q = q := by
  have hm : residualMass s η q = 1 - (s.card : ℝ) * η := by
    simp only [residualMass, Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul]
  funext i
  by_cases hi : i ∈ s
  · simp only [projectToFace, if_pos hi, hm, mul_div_cancel_right₀ _ hden]
    ring
  · simp only [projectToFace, if_neg hi, hsupport i hi]

theorem residualMass_projectToFace {r s : Finset ι} (hrs : r ⊆ s)
    (η : ℝ) (q : ι → ℝ) :
    residualMass r η (projectToFace s η q) =
      residualMass r η q * (1 - (s.card : ℝ) * η) / residualMass s η q := by
  unfold residualMass
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [projectToFace, if_pos (hrs hi), add_sub_cancel_left, residualMass]

theorem projectToFace_projectToFace {r s : Finset ι} (hrs : r ⊆ s)
    (η : ℝ) (q : ι → ℝ) (hden : 1 - (s.card : ℝ) * η ≠ 0)
    (hr : residualMass r η q ≠ 0) (hs : residualMass s η q ≠ 0) :
    projectToFace r η (projectToFace s η q) = projectToFace r η q := by
  funext i
  by_cases hi : i ∈ r
  · simp only [projectToFace, if_pos hi, if_pos (hrs hi), add_sub_cancel_left]
    rw [residualMass_projectToFace hrs]
    have hden' : 1 - η * (s.card : ℝ) ≠ 0 := by simpa only [mul_comm] using hden
    field_simp [hden', hr, hs]
  · simp only [projectToFace, if_neg hi]

end StdSimplexCore
