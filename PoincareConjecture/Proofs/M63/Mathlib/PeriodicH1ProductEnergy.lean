import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Coordinates

set_option autoImplicit false

open AddCircle MeasureTheory

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

theorem periodicH1Coordinates_product_bound (f f1 g g1 : C(AddCircle L, ℂ))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (f1 (x : AddCircle L)) x)
    (hg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => g (y : AddCircle L)) (g1 (x : AddCircle L)) x) :
    ∃ hfg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (f * g) (y : AddCircle L))
      ((f1 * g + f * g1) (x : AddCircle L)) x,
      ‖periodicH1Coordinates (f * g) (f1 * g + f * g1) hfg‖ ≤
        2 * (‖f‖ * ‖periodicH1Coordinates g g1 hg‖ +
          ‖g‖ * ‖periodicH1Coordinates f f1 hf‖) := by
  have hfg : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (f * g) (y : AddCircle L))
      ((f1 * g + f * g1) (x : AddCircle L)) x := by
    intro x
    simpa only [ContinuousMap.mul_apply, ContinuousMap.add_apply] using (hf x).fun_mul (hg x)
  refine ⟨hfg, ?_⟩
  have hi (h : C(AddCircle L, ℂ)) : Integrable (fun x => ‖h x‖ ^ 2) haarAddCircle :=
    (h.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hn (h : C(AddCircle L, ℂ)) : 0 ≤ ∫ x : AddCircle L, ‖h x‖ ^ 2 ∂haarAddCircle :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hmul (a b : C(AddCircle L, ℂ)) :
      (∫ x : AddCircle L, ‖(a * b) x‖ ^ 2 ∂haarAddCircle) ≤
        ‖a‖ ^ 2 * ∫ x : AddCircle L, ‖b x‖ ^ 2 ∂haarAddCircle := by
    rw [← integral_const_mul]
    apply integral_mono (hi (a * b)) ((hi b).const_mul _)
    intro x
    simp only [ContinuousMap.mul_apply, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (a.norm_coe_le_norm x) 2) (sq_nonneg _)
  have hadd (a b : C(AddCircle L, ℂ)) :
      (∫ x : AddCircle L, ‖(a + b) x‖ ^ 2 ∂haarAddCircle) ≤
        2 * (∫ x : AddCircle L, ‖a x‖ ^ 2 ∂haarAddCircle) +
          2 * ∫ x : AddCircle L, ‖b x‖ ^ 2 ∂haarAddCircle := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hi a).const_mul 2) ((hi b).const_mul 2)]
    apply integral_mono (hi (a + b)) (((hi a).const_mul 2).add ((hi b).const_mul 2))
    intro x
    have htri : ‖a x + b x‖ ^ 2 ≤ (‖a x‖ + ‖b x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    change ‖a x + b x‖ ^ 2 ≤ 2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have h0 := hmul f g
  have h1 := hmul g f1
  rw [mul_comm g f1] at h1
  have h2 := hmul f g1
  have h3 := hadd (f1 * g) (f * g1)
  have he := periodicH1Coordinates_norm_sq (f * g) (f1 * g + f * g1) hfg
  have hef := periodicH1Coordinates_norm_sq f f1 hf
  have heg := periodicH1Coordinates_norm_sq g g1 hg
  have hs : ‖periodicH1Coordinates (f * g) (f1 * g + f * g1) hfg‖ ^ 2 ≤
      2 * (‖f‖ * ‖periodicH1Coordinates g g1 hg‖) ^ 2 +
        2 * (‖g‖ * ‖periodicH1Coordinates f f1 hf‖) ^ 2 := by
    rw [he, mul_pow, mul_pow, hef, heg]
    nlinarith [mul_nonneg (sq_nonneg ‖f‖) (hn g),
      mul_nonneg (sq_nonneg ‖g‖) (hn f)]
  have ha : 0 ≤ ‖f‖ * ‖periodicH1Coordinates g g1 hg‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ ‖g‖ * ‖periodicH1Coordinates f f1 hf‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_nonneg ha hb, norm_nonneg (periodicH1Coordinates (f * g) (f1 * g + f * g1) hfg)]

end PoincareConjecture.M63
