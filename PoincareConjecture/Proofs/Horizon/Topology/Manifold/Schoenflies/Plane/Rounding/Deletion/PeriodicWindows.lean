import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Function

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem periodic_deriv_of_differentiable {f : ℝ → E} {T : ℝ}
    (hf : Differentiable ℝ f) (hper : Periodic f T) : Periodic (deriv f) T := by
  intro t
  have hd := (hf (t + T)).hasDerivAt.scomp t ((hasDerivAt_id t).add_const T)
  have heq : (fun s => f (s + T)) = f := funext hper
  simpa only [Function.comp_def, one_smul, id_eq, heq] using hd.deriv.symm

theorem exists_positive_derivatives_on_integer_window_of_periodic
    {n : ℕ} (hn : 0 < n) {α β : ℝ → E} {r : ℝ}
    (hα : Differentiable ℝ α) (hβ : Differentiable ℝ β)
    (hαper : Periodic α (n : ℝ)) (hβper : Periodic β (n : ℝ))
    (hfinite : ∀ i : ℤ, 0 ≤ i → i < (n : ℤ) →
      ∃ ℓ : E →L[ℝ] ℝ, ∀ t : ℝ, |t - (i : ℝ)| < r →
        0 < ℓ (deriv α t) ∧ 0 < ℓ (deriv β t)) :
    ∀ i : ℤ, ∃ ℓ : E →L[ℝ] ℝ, ∀ t : ℝ, |t - (i : ℝ)| < r →
      0 < ℓ (deriv α t) ∧ 0 < ℓ (deriv β t) := by
  intro i
  have hn' : 0 < (n : ℤ) := by exact_mod_cast hn
  obtain ⟨ℓ, hℓ⟩ := hfinite (i % n) (Int.emod_nonneg _ (ne_of_gt hn'))
    (Int.emod_lt_of_pos _ hn')
  refine ⟨ℓ, fun t ht => ?_⟩
  have hi : (i : ℝ) = ((i % n : ℤ) : ℝ) + ((i / n : ℤ) : ℝ) * (n : ℝ) := by
    exact_mod_cast (Int.emod_add_ediv_mul i (n : ℤ)).symm
  have ht' : |(t - ((i / n : ℤ) : ℝ) * (n : ℝ)) - ((i % n : ℤ) : ℝ)| < r := by
    convert ht using 2
    linarith
  have hαder := periodic_deriv_of_differentiable hα hαper
  have hβder := periodic_deriv_of_differentiable hβ hβper
  simpa only [hαder.sub_int_mul_eq (i / n), hβder.sub_int_mul_eq (i / n)] using
    hℓ (t - ((i / n : ℤ) : ℝ) * (n : ℝ)) ht'

end Poincare.Manifold.Schoenflies.Plane
