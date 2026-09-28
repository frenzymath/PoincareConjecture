import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.CircleRimReparametrization

set_option autoImplicit false
open Set Metric Topology
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

open PoincareConjecture Poincare.Manifold.Schoenflies

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem squareRimLoop_class_ne_one :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk squareRimLoop) ≠ 1 := by
  intro hclass
  have hnull : squareRimLoop.Homotopic (Path.refl squareRimBase) :=
    Path.Homotopic.Quotient.eq.mp hclass
  let p : Path (unitCircleExp 0) (unitCircleExp 0) := {
    toFun := fun t ↦ unitCircleExp (t : ℝ)
    continuous_toFun := contMDiff_unitCircleExp.continuous.comp continuous_subtype_val
    source' := rfl
    target' := by simpa using unitCircleExp_periodic 0 }
  obtain ⟨gamma, hgamma⟩ := exists_squareRimMap p
  have hbase : gamma squareRimBase = unitCircleExp 0 := by
    simpa using hgamma 0
  have hmapped := hnull.map gamma
  have hleft : (squareRimLoop.map gamma.continuous).toContinuousMap = p.toContinuousMap := by
    apply ContinuousMap.ext
    intro t
    exact hgamma t
  have hright : ((Path.refl squareRimBase).map gamma.continuous).toContinuousMap =
      ContinuousMap.const unitInterval (unitCircleExp 0) := by
    apply ContinuousMap.ext
    intro t
    exact hbase
  change (squareRimLoop.map gamma.continuous).toContinuousMap.HomotopicRel
    ((Path.refl squareRimBase).map gamma.continuous).toContinuousMap {0, 1} at hmapped
  rw [hleft, hright] at hmapped
  have hlift := isCoveringMap_unitCircleExp.liftPath_apply_one_eq_of_homotopicRel
    hmapped 0 rfl rfl
  have hpLift : (fun t : unitInterval ↦ (t : ℝ)) =
      isCoveringMap_unitCircleExp.liftPath p.toContinuousMap 0 rfl :=
    (isCoveringMap_unitCircleExp.eq_liftPath_iff rfl).mpr
      ⟨continuous_subtype_val, rfl, rfl⟩
  have hcLift : isCoveringMap_unitCircleExp.liftPath
      (ContinuousMap.const unitInterval (unitCircleExp 0)) 0 rfl =
        ContinuousMap.const unitInterval (0 : ℝ) :=
    isCoveringMap_unitCircleExp.liftPath_const rfl
  rw [← hpLift, hcLift] at hlift
  exact one_ne_zero hlift

theorem squareRimLoop_map_class_ne_one_of_retraction
    {Y : Type*} [TopologicalSpace Y]
    (gamma : C(Q2, Y)) (retract : C(Y, Q2))
    (hleft : ∀ x, retract (gamma x) = x) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1 := by
  intro hclass
  have hnull : (squareRimLoop.map gamma.continuous).Homotopic
      (Path.refl (gamma squareRimBase)) := Path.Homotopic.Quotient.eq.mp hclass
  have h := hnull.map retract
  have hpath : ((squareRimLoop.map gamma.continuous).map retract.continuous).toContinuousMap =
      squareRimLoop.toContinuousMap := ContinuousMap.ext (fun t ↦ hleft (squareRimLoop t))
  have hconst : ((Path.refl (gamma squareRimBase)).map retract.continuous).toContinuousMap =
      (Path.refl squareRimBase).toContinuousMap :=
    ContinuousMap.ext (fun _ ↦ hleft squareRimBase)
  change ((squareRimLoop.map gamma.continuous).map retract.continuous).toContinuousMap.HomotopicRel
    ((Path.refl (gamma squareRimBase)).map retract.continuous).toContinuousMap {0, 1} at h
  rw [hpath, hconst] at h
  exact squareRimLoop_class_ne_one (Path.Homotopic.Quotient.eq.mpr h)

end PoincareConjecture.M76.Dehn
