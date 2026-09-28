import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronChainCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {α β : Type*}

theorem dual_restrict_injective (i : α ↪ β) :
    Function.Injective (LinearMap.funLeft (ZMod 2) (ZMod 2) i).dualMap :=
  LinearMap.dualMap_injective_of_surjective
    (LinearMap.funLeft_surjective_of_injective _ _ i i.injective)

open Classical in

theorem dual_restrict_single_image (i : α ↪ β)
    (c : Module.Dual (ZMod 2) (α → ZMod 2)) (a : α) :
    (LinearMap.funLeft (ZMod 2) (ZMod 2) i).dualMap c (Pi.single (i a) 1) =
      c (Pi.single a 1) := by
  change c (fun x => (Pi.single (i a) 1 : β → ZMod 2) (i x)) = c (Pi.single a 1)
  congr 1
  funext x
  simp only [Pi.single_apply, i.injective.eq_iff]

open Classical in

theorem dual_restrict_single_off_range (i : α ↪ β)
    (c : Module.Dual (ZMod 2) (α → ZMod 2)) {b : β} (hb : b ∉ Set.range i) :
    (LinearMap.funLeft (ZMod 2) (ZMod 2) i).dualMap c (Pi.single b 1) = 0 := by
  have hzero : (fun x => (Pi.single b 1 : β → ZMod 2) (i x)) = (0 : α → ZMod 2) := by
    funext x
    have hi : i x ≠ b := fun h => hb ⟨x, h⟩
    simp only [Pi.single_apply, if_neg hi, Pi.zero_apply]
  change c (fun x => (Pi.single b 1 : β → ZMod 2) (i x)) = 0
  rw [hzero, map_zero]

open Classical in

theorem dual_restrict_range_iff [Finite β] (i : α ↪ β)
    (c : Module.Dual (ZMod 2) (β → ZMod 2)) :
    c ∈ LinearMap.range (LinearMap.funLeft (ZMod 2) (ZMod 2) i).dualMap ↔
      ∀ b : β, b ∉ Set.range i → c (Pi.single b 1) = 0 := by
  let : Fintype β := Fintype.ofFinite β
  constructor
  · rintro ⟨d, rfl⟩ b hb
    exact dual_restrict_single_off_range i d hb
  · intro hsupport
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective
      (LinearMap.funLeft (ZMod 2) (ZMod 2) i)
      (LinearMap.funLeft_surjective_of_injective _ _ i i.injective)]
    apply (Submodule.mem_dualAnnihilator c).mpr
    intro f hf
    have hfzero : LinearMap.funLeft (ZMod 2) (ZMod 2) i f = 0 := hf
    rw [dual_apply_eq_sum_coordinates]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b ∈ Set.range i
    · obtain ⟨a, rfl⟩ := hb
      have hz : f (i a) = 0 := congrFun hfzero a
      rw [hz, zero_mul]
    · rw [hsupport b hb, mul_zero]

end PreAbstractSimplicialComplex.ModTwoCochains
