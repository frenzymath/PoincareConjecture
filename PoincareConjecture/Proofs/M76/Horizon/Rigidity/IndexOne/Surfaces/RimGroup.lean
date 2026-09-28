import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.SourceRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.General.LatticeHandleBoundaryGroups

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "D" => closedBall (0 : V1) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem sourceRim_ambient_pi1_injective (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (x : ↥(sourceSurface phi theta ∩ frontier R)) :
    Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(sourceSurface phi theta ∩ frontier R), X)) x) := by
  let S : Set D := {a | ‖(a : V1)‖ = 1}
  let : Finite S := (finite_unit_rim_of_card_eq_one (ι := Fin 1) (by simp)).to_subtype
  let E : hamiltonOneAnnulusRim ≃ₜ (S × C) := {
    toFun := fun z => (⟨z.val.1, z.property⟩, z.val.2)
    invFun := fun z => ⟨(z.1.val, z.2), z.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let q : ↥(sourceSurface phi theta ∩ frontier R) ≃ₜ (S × C) :=
    (sourceRimCoordinates phi theta F).trans E
  let r : C(X, C) := ⟨fun y => hamiltonLowerLatticePiEquiv (Fin 2) y.2 0,
    (continuous_apply 0).comp
      ((hamiltonLowerLatticePiEquiv (Fin 2)).continuous.comp continuous_snd)⟩
  let i : C(↥(sourceSurface phi theta ∩ frontier R), X) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  have hq : Function.Injective (FundamentalGroup.map ⟨q, q.continuous⟩ x) :=
    FundamentalGroup.map_injective_of_leftInverse ⟨q, q.continuous⟩
      ⟨q.symm, q.symm.continuous⟩ q.symm_apply_apply x
  intro a b hab
  apply hq
  apply FundamentalGroup.map_snd_injective_of_totallyDisconnected (q x)
  have hc := FundamentalGroup.map_comp_apply ⟨q, q.continuous⟩
    (⟨Prod.snd, continuous_snd⟩ : C(S × C, C)) x
  have hr : FundamentalGroup.map (r.comp i) x a =
      FundamentalGroup.map (r.comp i) x b := by
    rw [FundamentalGroup.map_comp_apply, FundamentalGroup.map_comp_apply]
    exact congrArg (FundamentalGroup.map r (i x)) hab
  exact (hc a).symm.trans (hr.trans (hc b))

end PoincareConjecture.M76.HamiltonIntervalTorus
