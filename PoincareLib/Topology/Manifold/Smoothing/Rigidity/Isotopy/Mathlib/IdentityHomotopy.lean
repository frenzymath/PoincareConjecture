import Mathlib.Topology.Homotopy.Equiv

/-!+# An actual identity inverse from a relative identity homotopy

The relative homotopy entering Hamilton 1976, Lemma 3, p. 65,
makes the supplied map a homotopy equivalence with literal identity
inverse. This construction uses only Mathlib's homotopy operations.
See M76 inputs/Rigidity/derivations/001_source_and_marked_maps.md.
-/

set_option autoImplicit false

universe u

namespace ContinuousMap.HomotopyRel

variable {X : Type u} [TopologicalSpace X] {f : C(X, X)} {S : Set X}

/-- A homotopy from the identity to the actual map supplies its
literal identity homotopy inverse. See Hamilton Lemma 3, p. 65,
and rigidity derivation 001, first formal stage 2. -/
def homotopyEquivOfId (F : (ContinuousMap.id X).HomotopyRel f S) :
    ContinuousMap.HomotopyEquiv X X where
  toFun := f
  invFun := ContinuousMap.id X
  left_inv := by
    simpa only [ContinuousMap.id_comp] using
      (show f.Homotopic (ContinuousMap.id X) from ⟨F.toHomotopy.symm⟩)
  right_inv := by
    simpa only [ContinuousMap.comp_id] using
      (show f.Homotopic (ContinuousMap.id X) from ⟨F.toHomotopy.symm⟩)

/-- The homotopy equivalence retains the supplied forward map
exactly. See rigidity derivation 001, first formal stage 2. -/
@[simp]
theorem homotopyEquivOfId_toFun (F : (ContinuousMap.id X).HomotopyRel f S) :
    F.homotopyEquivOfId.toFun = f := rfl

/-- The chosen inverse is the literal identity continuous map.
See rigidity derivation 001, first formal stage 2. -/
@[simp]
theorem homotopyEquivOfId_invFun (F : (ContinuousMap.id X).HomotopyRel f S) :
    F.homotopyEquivOfId.invFun = ContinuousMap.id X := rfl

end ContinuousMap.HomotopyRel
