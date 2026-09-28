import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveInduction









set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




def recenter (P : AlexanderSectionProfile E) (c : ℝ) : AlexanderSectionProfile E where
  carrier := P.carrier
  height := P.height - AffineMap.const ℝ E c
  charge := fun d => P.charge (d + c)
  presentation d := by
    change HasAlexanderCurvePresentation
      (P.carrier ∩ {x | P.height x - c = d}) (P.charge (d + c))
    simpa only [sub_eq_iff_eq_add] using P.presentation (d + c)
  finite_support := by
    change ((fun d : ℝ => d + c) ⁻¹' Function.support P.charge).Finite
    exact P.finite_support.preimage (fun _ _ _ _ h => add_right_cancel h)


@[simp] theorem recenter_carrier (P : AlexanderSectionProfile E) (c : ℝ) :
    (P.recenter c).carrier = P.carrier := rfl



@[simp] theorem recenter_height_apply (P : AlexanderSectionProfile E) (c : ℝ) (x : E) :
    (P.recenter c).height x = P.height x - c := rfl



@[simp] theorem recenter_charge_apply (P : AlexanderSectionProfile E) (c d : ℝ) :
    (P.recenter c).charge d = P.charge (d + c) := rfl




@[simp] theorem complexity_recenter (P : AlexanderSectionProfile E) (c : ℝ) :
    (P.recenter c).complexity = P.complexity := by
  classical
  unfold complexity
  refine Finset.sum_bij (fun d _ => d + c) ?_ ?_ ?_ ?_
  · intro d hd
    exact P.finite_support.mem_toFinset.mpr
      ((P.recenter c).finite_support.mem_toFinset.mp hd)
  · intro d _ e _ h
    exact add_right_cancel h
  · intro d hd
    have hmem : d - c ∈ (P.recenter c).finite_support.toFinset := by
      apply (P.recenter c).finite_support.mem_toFinset.mpr
      change P.charge (d - c + c) ≠ 0
      simpa only [sub_add_cancel, Function.mem_support] using P.finite_support.mem_toFinset.mp hd
    exact ⟨d - c, hmem, sub_add_cancel d c⟩
  · exact fun _ _ => rfl

end Geometry.AlexanderSectionProfile
