import Mathlib.GroupTheory.Perm.Cycle.Type



set_option autoImplicit false

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_cycleType_eq_card_orbits_of_no_fixed_points (f : Perm α)
    (hf : ∀ x, f x ≠ x) :
    f.cycleType.card = Nat.card (Quotient (SameCycle.setoid f)) := by
  classical
  let g : Quotient (SameCycle.setoid f) → f.cycleFactorsFinset :=
    Quotient.lift (fun x => ⟨f.cycleOf x,
      cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr (hf x))⟩)
      (fun _ _ h => Subtype.ext h.cycleOf_eq)
  have hgi : Function.Injective g := by
    intro x y h
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        apply Quotient.sound
        exact (sameCycle_iff_cycleOf_eq_of_mem_support
          (mem_support.mpr (hf x)) (mem_support.mpr (hf y))).mpr (congrArg Subtype.val h)
  have hgs : Function.Surjective g := by
    intro c
    obtain ⟨x, hx⟩ := (mem_cycleFactorsFinset_iff.mp c.property).1.nonempty_support
    refine ⟨Quotient.mk _ x, Subtype.ext ?_⟩
    exact (cycle_is_cycleOf hx c.property).symm
  have hc := Nat.card_congr (Equiv.ofBijective g ⟨hgi, hgs⟩)
  simpa [cycleType] using hc.symm

theorem sign_eq_pow_card_add_orbits_of_no_fixed_points (f : Perm α)
    (hf : ∀ x, f x ≠ x) :
    sign f = (-1 : ℤˣ) ^ (Fintype.card α + Nat.card (Quotient (SameCycle.setoid f))) := by
  have hs : f.support = Finset.univ := by
    ext x
    simp [mem_support, hf x]
  rw [sign_of_cycleType, sum_cycleType, hs, Finset.card_univ,
    card_cycleType_eq_card_orbits_of_no_fixed_points f hf]

end Equiv.Perm
