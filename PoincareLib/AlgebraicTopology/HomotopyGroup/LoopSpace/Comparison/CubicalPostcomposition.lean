import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology

/-!
# Multiplication under cubical postcomposition

Continuous postcomposition preserves the concatenation formulas on actual
cube representatives. Source: Hatcher, Section 4.1, pp. 340-342.
-/

set_option autoImplicit false

open scoped Topology unitInterval

namespace PoincareMT.Proofs.M59

open PoincareMT.Proofs.M02

variable {N X Y : Type*} [DecidableEq N] [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Postcomposition commutes with concatenation in each cube coordinate.
Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem mapGenLoop_transAt (f : C(X, Y)) (h : f x = y) (i : N)
    (a b : GenLoop N X x) :
    mapGenLoop f h (GenLoop.transAt i a b) =
      GenLoop.transAt i (mapGenLoop f h a) (mapGenLoop f h b) := by
  ext v
  change f ((GenLoop.transAt i a b) v) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- Continuous postcomposition is a homomorphism on nonzero homotopy groups.
Source: Hatcher, Section 4.1, pp. 340-342. -/
noncomputable def homotopyGroupMapHom [Nonempty N] (f : C(X, Y)) (h : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := homotopyGroupMap N f h
  map_one' := by
    change (⟦mapGenLoop f h GenLoop.const⟧ : HomotopyGroup N Y y) = ⟦GenLoop.const⟧
    exact congrArg (fun a => (⟦a⟧ : HomotopyGroup N Y y)) (by ext v; exact h)
  map_mul' a b := Quotient.inductionOn₂ a b fun a b => by
    let i : N := Classical.choice inferInstance
    exact (congrArg (homotopyGroupMap N f h)
      (HomotopyGroup.mul_spec (i := i) (p := a) (q := b))).trans
      ((congrArg (fun a => (⟦a⟧ : HomotopyGroup N Y y))
        (mapGenLoop_transAt f h i b a)).trans (HomotopyGroup.mul_spec (i := i)).symm)

end PoincareMT.Proofs.M59
