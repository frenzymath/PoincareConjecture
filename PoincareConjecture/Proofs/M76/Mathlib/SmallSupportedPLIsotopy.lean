import PoincareConjecture.Proofs.M76.Mathlib.SmallSupportedPLDeformation
import PoincareConjecture.Proofs.M76.Mathlib.ContinuousInverseFamily











set_option autoImplicit false

open Set Geometry
open scoped NNReal

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem FinitePiecewiseAffineOn.exists_small_supported_isotopy
    {f : E → E} {C : Set E} (hf : FinitePiecewiseAffineOn f C) (hcv : Convex ℝ C)
    (hzero : ∀ x ∈ frontier C, f x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
      Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
      Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
      (∀ (t : Icc (-ε) ε) (x : E), H t x = x + (t : ℝ) • C.indicator f x) ∧
      ∀ t : Icc (-ε) ε, (∀ x, x ∉ interior C → H t x = x) ∧ H t '' C = C ∧
        ∃ e : C ≃ₜ C, e.IsFinitePL ∧ ∀ x : C, (e x : E) = H t x := by
  classical
  obtain ⟨δ, hδ, hdeform⟩ := hf.exists_small_supported_deformation hcv hzero
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith hcv
  have hcopy := hf
  obtain ⟨K, hK, hKC, _⟩ := hcopy
  have hCc : IsClosed C := by
    rw [← hKC]
    exact (K.isCompact_space_of_finite hK).isClosed
  have hu := hL.indicator_of_eq_zero_frontier hCc hzero
  let η : ℝ := ((L : ℝ) + 1)⁻¹ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : η * ((L : ℝ) + 1) = 1 / 2 := by
    have hpos : 0 < (L : ℝ) + 1 := by positivity
    dsimp [η]
    field_simp
  let ε := min δ η
  have hε : 0 < ε := lt_min hδ hη
  have htδ (t : Icc (-ε) ε) : |(t : ℝ)| ≤ δ :=
    (abs_le.mpr t.property).trans (min_le_left _ _)
  choose H hH using fun t : Icc (-ε) ε => hdeform t (htδ t)
  have hformula (t : Icc (-ε) ε) (x : E) :
      H t x = x + (t : ℝ) • C.indicator f x := by
    by_cases hx : x ∈ C
    · rw [indicator_of_mem hx]
      exact (hH t).1 x hx
    · rw [indicator_of_notMem hx, smul_zero, add_zero]
      exact (hH t).2.1 x (fun hi => hx (interior_subset hi))
  have hcont : Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) := by
    simp_rw [hformula]
    exact continuous_snd.add ((continuous_subtype_val.comp continuous_fst).smul
      (hu.continuous.comp continuous_snd))
  have hanti (t : Icc (-ε) ε) : AntilipschitzWith 2 (H t) := by
    have htη : |(t : ℝ)| ≤ η := (abs_le.mpr t.property).trans (min_le_right _ _)
    have hsmall : |(t : ℝ)| * (L : ℝ) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_right htη L.coe_nonneg).trans (by nlinarith)
    have heq : (H t : E → E) = fun x => x + (t : ℝ) • C.indicator f x :=
      funext (hformula t)
    rw [heq]
    exact hu.antilipschitzWith_id_add_smul hsmall
  exact ⟨ε, hε, H, hcont, Homeomorph.continuous_symm_family_of_antilipschitz H hcont hanti,
    hformula, fun t => (hH t).2⟩

end Geometry
