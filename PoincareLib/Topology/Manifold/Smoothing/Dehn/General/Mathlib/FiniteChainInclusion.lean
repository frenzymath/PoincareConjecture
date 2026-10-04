import PoincareLib.Topology.Manifold.Smoothing.Dehn.Coordinates.Mathlib.TetrahedronChainCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Exact coordinates of the original chain inclusion

Dual restriction along the actual face injection retains each marked
coefficient and vanishes at every other face. Its range is exactly
the chains with that whole marked support. See Dehn derivation 018
and Hatcher pp. 104--107, 189--190.
-/

set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {α β : Type*}

/-- Surjective restriction along the actual face embedding makes
its dual inclusion injective. See Dehn derivation 018. -/
theorem dual_restrict_injective (i : α ↪ β) :
    Function.Injective (LinearMap.funLeft (ZMod 2) (ZMod 2) i).dualMap :=
  LinearMap.dualMap_injective_of_surjective
    (LinearMap.funLeft_surjective_of_injective _ _ i i.injective)

open Classical in
/-- The coefficient at the actual image face is unchanged.
See Dehn derivation 018. -/
theorem dual_restrict_single_image (i : α ↪ β)
    (c : Module.Dual (ZMod 2) (α → ZMod 2)) (a : α) :
    (LinearMap.funLeft (ZMod 2) (ZMod 2) i).dualMap c (Pi.single (i a) 1) =
      c (Pi.single a 1) := by
  change c (fun x => (Pi.single (i a) 1 : β → ZMod 2) (i x)) = c (Pi.single a 1)
  congr 1
  funext x
  simp only [Pi.single_apply, i.injective.eq_iff]

open Classical in
/-- Every coefficient outside the whole original face image is zero.
See Dehn derivation 018. -/
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
/-- The dual inclusion has exactly the full marked support.
The converse uses finite original coordinate expansion and the
proved annihilator identity. See Dehn derivation 018. -/
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
