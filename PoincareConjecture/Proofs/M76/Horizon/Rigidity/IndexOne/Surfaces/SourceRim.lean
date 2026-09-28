import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.SourceSurface











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))



noncomputable def sourceRimCoordinates (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ↥(sourceSurface phi theta ∩ frontier R) ≃ₜ hamiltonOneAnnulusRim := by
  let E := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  have hB (x : R) : E x ∈ B ↔ (x : X) ∈ frontier R :=
    Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary (Fin 1) (Fin 2) L) x
  let f : ↥(sourceSurface phi theta ∩ frontier R) → hamiltonOneAnnulusRim :=
    fun z => ⟨(hamiltonOneHierarchyCoordinates
      (E ⟨z.val, sourceSurface_subset phi theta z.property.1⟩)).1,
        ((hB ⟨z.val, sourceSurface_subset phi theta z.property.1⟩).mpr z.property.2).1⟩
  let g : hamiltonOneAnnulusRim → ↥(sourceSurface phi theta ∩ frontier R) := fun z => by
    let x := hamiltonOneHierarchyCoordinates.symm (z.val, theta)
    have hxB : x ∈ B := ⟨z.property, mem_univ _⟩
    have hxphase : sourcePhase phi x = theta := by
      rw [sourcePhase_eq_on_boundary phi F x hxB]
      exact congrArg Prod.snd (hamiltonOneHierarchyCoordinates.apply_symm_apply (z.val, theta))
    refine ⟨E.symm x, ?_, ?_⟩
    · apply (mem_sourceSurface_iff phi theta (E.symm x)).mpr
      rw [E.apply_symm_apply]
      exact hxphase
    · apply (hB (E.symm x)).mp
      simpa only [E.apply_symm_apply] using hxB
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := by fun_prop
    continuous_invFun := by
      apply Continuous.subtype_mk
      change Continuous (fun z : hamiltonOneAnnulusRim =>
        (E.symm (hamiltonOneHierarchyCoordinates.symm (z.val, theta)) : X))
      fun_prop
  }
  · intro z
    apply Subtype.ext
    change (E.symm (hamiltonOneHierarchyCoordinates.symm
      ((hamiltonOneHierarchyCoordinates (E ⟨z.val,
        sourceSurface_subset phi theta z.property.1⟩)).1, theta)) : X) = z.val
    let x : R := ⟨z.val, sourceSurface_subset phi theta z.property.1⟩
    have hxphase := (mem_sourceSurface_iff phi theta x).mp z.property.1
    have hxB := (hB x).mpr z.property.2
    have hcoord : (hamiltonOneHierarchyCoordinates (E x)).2 = theta :=
      (sourcePhase_eq_on_boundary phi F (E x) hxB).symm.trans hxphase
    have hpair : ((hamiltonOneHierarchyCoordinates (E x)).1, theta) =
        hamiltonOneHierarchyCoordinates (E x) := Prod.ext rfl hcoord.symm
    change (E.symm (hamiltonOneHierarchyCoordinates.symm
      ((hamiltonOneHierarchyCoordinates (E x)).1, theta)) : X) = z.val
    rw [hpair, hamiltonOneHierarchyCoordinates.symm_apply_apply, E.symm_apply_apply]
  · intro z
    apply Subtype.ext
    change (hamiltonOneHierarchyCoordinates
      (E (E.symm (hamiltonOneHierarchyCoordinates.symm (z.val, theta))))).1 = z.val
    rw [E.apply_symm_apply, hamiltonOneHierarchyCoordinates.apply_symm_apply]


theorem sourceRimCoordinates_symm_original_point (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (z : hamiltonOneAnnulusRim) :
    ((sourceRimCoordinates phi theta F).symm z : X) =
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
        (hamiltonOneHierarchyCoordinates.symm (z.val, theta)) : X) := rfl

end PoincareConjecture.M76.HamiltonIntervalTorus
