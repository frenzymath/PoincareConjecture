import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.ScalarTranslation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.BoundaryPhaseCover
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourcePhaseSets

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem translatedMap_phase (phi : C(H, H)) (w : C(X, ℝ)) (x : H) :
    sourcePhase (translatedMap phi w) x = sourcePhase phi x +
      ((w ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X)) : C) :=
  congrArg Prod.snd (handleTranslation_coordinates _ _)

theorem translatedMap_fst (phi : C(H, H)) (w : C(X, ℝ)) (x : H) :
    (translatedMap phi w x).1 = (phi x).1 := rfl

theorem ambientSourcePhase_translatedMap (phi : C(H, H)) (w : C(X, ℝ)) (x : R) :
    ambientSourcePhase (translatedMap phi w) x = ambientSourcePhase phi x + (w x : C) := by
  rw [ambientSourcePhase_domain, ambientSourcePhase_domain, translatedMap_phase,
    Homeomorph.symm_apply_apply]

theorem translatedMap_preimage_boundary (phi : C(H, H)) (w : C(X, ℝ)) :
    translatedMap phi w ⁻¹' B = phi ⁻¹' B := by
  ext x
  rfl

noncomputable def scalarHomotopy (phi : C(H, H)) (w : C(X, ℝ))
    (hw : ∀ x ∈ frontier R, w x = 0) : phi.HomotopyRel (translatedMap phi w) B where
  toFun z := handleTranslation
    ((z.1 : ℝ) * w ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm z.2 : X), phi z.2)
  continuous_toFun := by fun_prop
  map_zero_left x := by
    change handleTranslation ((0 : ℝ) * _, phi x) = phi x
    rw [zero_mul, handleTranslation_zero]
  map_one_left x := by
    change handleTranslation ((1 : ℝ) * _, phi x) = handleTranslation (_, phi x)
    rw [one_mul]
  prop' := by
    intro t x hx
    have hfront : ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∈ frontier R := by
      apply (Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary (Fin 1) (Fin 2) L)
        ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x)).mp
      change latticeHandleDomainEquiv (Fin 1) (Fin 2) L
        ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x) ∈ B
      rwa [Homeomorph.apply_symm_apply]
    change handleTranslation ((t : ℝ) * w _, phi x) = phi x
    rw [hw _ hfront, mul_zero, handleTranslation_zero]

theorem scalarHomotopy_fixed (phi : C(H, H)) (w : C(X, ℝ))
    (hw : ∀ x ∈ frontier R, w x = 0) (t : unitInterval) (x : H)
    (hx : w ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) = 0) :
    scalarHomotopy phi w hw (t, x) = phi x := by
  change handleTranslation ((t : ℝ) * w _, phi x) = phi x
  rw [hx, mul_zero, handleTranslation_zero]

theorem translatedMap_relative_properties
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (w : C(X, ℝ))
    (hwPL : ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target)
    (hw : ∀ x ∈ frontier R, w x = 0) :
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L (translatedMap phi w)) ∧
      Nonempty (phi.HomotopyRel (translatedMap phi w) B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel (translatedMap phi w) B) ∧
      translatedMap phi w ⁻¹' B = phi ⁻¹' B :=
  ⟨chartwisePL_translatedMap hd hphi w hwPL, ⟨scalarHomotopy phi w hw⟩,
    ⟨F.trans (scalarHomotopy phi w hw)⟩, translatedMap_preimage_boundary phi w⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
