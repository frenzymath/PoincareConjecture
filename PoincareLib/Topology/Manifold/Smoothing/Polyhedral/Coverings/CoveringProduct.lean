import Mathlib.Topology.Covering.Basic

/-!
# Products of covering maps with an identity

An evenly covered neighborhood stays evenly covered after
taking its product with any parameter space. This constructs
Hamilton's handle-base product covering, p. 67. See M76
derivation 89.
-/

set_option autoImplicit false

open Set

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A] {p : E → X}

/-- Product with the identity preserves an evenly covered
neighborhood and its discrete fiber. See Hamilton p. 67 and
M76 derivation 89. -/
theorem IsEvenlyCovered.id_prod {x : X} {F : Type*} [TopologicalSpace F]
    (h : IsEvenlyCovered p x F) (a : A) :
    IsEvenlyCovered (Prod.map id p) (a, x) F := by
  obtain ⟨hF, U, hxU, hU, hpU, H, hH⟩ := h
  let V : Set (A × X) := Prod.snd ⁻¹' U
  let e₀ : (Prod.map id p ⁻¹' V) ≃ₜ (A × (p ⁻¹' U)) :=
    { toFun y := (y.1.1, ⟨y.1.2, y.2⟩)
      invFun y := ⟨(y.1, y.2.1), y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₁ : (A × U) ≃ₜ V :=
    { toFun y := ⟨(y.1, y.2.1), y.2.2⟩
      invFun y := (y.1.1, ⟨y.1.2, y.2⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨hF, V, hxU, hU.preimage continuous_snd, hpU.preimage continuous_snd,
    e₀.trans (((Homeomorph.refl A).prodCongr H).trans
      ((Homeomorph.prodAssoc A U F).symm.trans
        (e₁.prodCongr (Homeomorph.refl F)))), ?_⟩
  intro y
  exact Prod.ext rfl (hH ⟨y.1.2, y.2⟩)

/-- A covering map remains a covering map after product with
the identity. See Hamilton p. 67 and M76 derivation 89. -/
theorem IsCoveringMap.id_prod (hp : IsCoveringMap p) :
    IsCoveringMap (Prod.map (id : A → A) p) :=
  fun y => ((hp y.2).id_prod y.1).to_isEvenlyCovered_preimage
