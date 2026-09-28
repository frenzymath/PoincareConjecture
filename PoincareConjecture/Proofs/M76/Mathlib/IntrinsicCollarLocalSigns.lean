import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.CollarBottomClosure

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AlexanderCollarSlab.mem_closure_positive_of_ne_apex
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) {x : E}
    (hx : x ∈ S ∩ {x | A x = 0}) (hxq : x ≠ q) :
    x ∈ closure (S ∩ {y | 0 < A y}) := by
  apply M.chart.collar_bottom_mem_closure_positive M.height M.bottom hx
    (M.upper_pos x hx hxq)
  intro p _ _
  exact (M.cover.subset (Or.inl (M.chart p).property)).1

theorem AlexanderCollarSlab.exists_both_signs_in_open
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
    {x : E} (hx : x ∈ S ∩ {x | A x = 0}) (hxq : x ≠ q)
    {U : Set E} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ y ∈ S ∩ U, ∃ z ∈ S ∩ U, 0 < A y ∧ A z < 0 := by
  have hpos := M.mem_closure_positive_of_ne_apex hx hxq
  have hxNeg : x ∈ S ∩ {x | (-A) x = 0} := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hx
  have hneg : x ∈ closure (S ∩ {y | A y < 0}) := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      Mneg.mem_closure_positive_of_ne_apex hxNeg hxq
  obtain ⟨y, hyU, hyS, hyA⟩ := mem_closure_iff.mp hpos U hU hxU
  obtain ⟨z, hzU, hzS, hzA⟩ := mem_closure_iff.mp hneg U hU hxU
  exact ⟨y, ⟨hyS, hyU⟩, z, ⟨hzS, hzU⟩, hyA, hzA⟩

end Geometry
