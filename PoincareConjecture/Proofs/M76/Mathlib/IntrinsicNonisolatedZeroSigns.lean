import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicCollarLocalSigns

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AlexanderCollarSlab.mem_closure_positive_of_zero_accumulation
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q x : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hx : x ∈ closure ((S ∩ {y | A y = 0}) \ {q})) :
    x ∈ closure (S ∩ {y | 0 < A y}) := by
  have hsub : (S ∩ {y | A y = 0}) \ {q} ⊆ closure (S ∩ {y | 0 < A y}) := by
    intro y hy
    exact M.mem_closure_positive_of_ne_apex hy.1 hy.2
  have h := closure_mono hsub hx
  rwa [closure_closure] at h

theorem AlexanderCollarSlab.mem_both_zero_height_closures_of_nonisolated_apex
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
    (hq : q ∈ closure ((S ∩ {y | A y = 0}) \ {q}))
    {x : E} (hx : x ∈ S ∩ {y | A y = 0}) :
    x ∈ closure (S ∩ {y | 0 < A y}) ∧
      x ∈ closure (S ∩ {y | A y < 0}) := by
  have hpos : x ∈ closure (S ∩ {y | 0 < A y}) := by
    by_cases hxq : x = q
    · subst x
      exact M.mem_closure_positive_of_zero_accumulation hq
    · exact M.mem_closure_positive_of_ne_apex hx hxq
  refine ⟨hpos, ?_⟩
  have hxNeg : x ∈ S ∩ {y | (-A) y = 0} := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hx
  have hneg : x ∈ closure (S ∩ {y | 0 < (-A) y}) := by
    by_cases hxq : x = q
    · subst x
      apply Mneg.mem_closure_positive_of_zero_accumulation
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hq
    · exact Mneg.mem_closure_positive_of_ne_apex hxNeg hxq
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hneg

end Geometry
