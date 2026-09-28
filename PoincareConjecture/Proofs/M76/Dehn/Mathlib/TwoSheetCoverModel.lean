import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homeomorph.TransferInstance
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.EquivFin












set_option autoImplicit false

universe u v

open Set

namespace CoveringTwoSheet




noncomputable def equivProduct {E : Type v} {X : Type u} (p : E → X)
    (htwo : ∀ x, (p ⁻¹' {x}).ncard = 2) : E ≃ X × Fin 2 := by
  classical
  let e : ∀ x, (p ⁻¹' {x}) ≃ Fin 2 := fun x => by
    letI := (finite_of_ncard_ne_zero (by rw [htwo x]; decide)).fintype
    exact Fintype.equivFinOfCardEq ((fintypeCard_eq_ncard _).trans (htwo x))
  exact (Equiv.sigmaPreimageEquiv p).symm.trans (Equiv.sigmaEquivProdOfEquiv e)



theorem fst_equivProduct {E : Type v} {X : Type u} (p : E → X)
    (htwo : ∀ x, (p ⁻¹' {x}).ncard = 2) (y : E) :
    (equivProduct p htwo y).1 = p y := rfl




theorem ncard_fiber_fst {X : Type u} (x : X) :
    ((Prod.fst : X × Fin 2 → X) ⁻¹' {x}).ncard = 2 := by
  let e : ((Prod.fst : X × Fin 2 → X) ⁻¹' {x}) ≃ Fin 2 :=
    { toFun := fun y => y.val.2
      invFun := fun b => ⟨(x, b), rfl⟩
      left_inv := fun y => Subtype.ext (Prod.ext y.property.symm rfl)
      right_inv := fun _ => rfl }
  change Nat.card ((Prod.fst : X × Fin 2 → X) ⁻¹' {x}) = 2
  rw [Nat.card_congr e, Nat.card_fin]

end CoveringTwoSheet

namespace IsCoveringMap






theorem exists_two_sheet_model
    {E : Type v} {X : Type u} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [ConnectedSpace E] {p : E → X} (hp : IsCoveringMap p)
    (htwo : ∀ x, (p ⁻¹' {x}).ncard = 2) :
    ∃ t : TopologicalSpace (X × Fin 2),
      letI := t
      ∃ H : (X × Fin 2) ≃ₜ E,
        (∀ z, p (H z) = z.1) ∧ T2Space (X × Fin 2) ∧
        ConnectedSpace (X × Fin 2) ∧
        IsCoveringMap (Prod.fst : X × Fin 2 → X) ∧
        ∀ x, ((Prod.fst : X × Fin 2 → X) ⁻¹' {x}).ncard = 2 := by
  let b := CoveringTwoSheet.equivProduct p htwo
  let : TopologicalSpace (X × Fin 2) := b.symm.topologicalSpace
  let H : (X × Fin 2) ≃ₜ E := b.symm.homeomorph
  have hH (z : X × Fin 2) : p (H z) = z.1 := by
    exact congrArg Prod.fst (b.apply_symm_apply z)
  have hT2 : T2Space (X × Fin 2) := H.symm.t2Space
  have hconn : ConnectedSpace (X × Fin 2) :=
    H.symm.surjective.connectedSpace H.symm.continuous
  have hproj : (p ∘ H) = (Prod.fst : X × Fin 2 → X) := funext hH
  have hcover : IsCoveringMap (Prod.fst : X × Fin 2 → X) := by
    rw [← hproj]
    exact hp.comp_homeomorph H
  exact ⟨inferInstance, H, hH, hT2, hconn, hcover, CoveringTwoSheet.ncard_fiber_fst⟩

end IsCoveringMap
