import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.SourceSurface

/-!
# The complete rim of the source phase

The given relative homotopy fixes each old boundary point. Consequently
the source phase has exactly the two prescribed boundary circles, with
their literal interval endpoint and first circle coordinate. This does
not classify the surface components. See Hamilton 1976, Lemma 3,
pp. 65--67, and Waldhausen 1968, Section 1.3, pp. 59--60.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

/-- Exact coordinates for the whole rim, preserving the actual old
boundary point rather than choosing boundary reparametrizations. -/
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

/-- The inverse rim coordinates retain the literal original handle point. -/
theorem sourceRimCoordinates_symm_original_point (phi : C(H, H)) (theta : C)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (z : hamiltonOneAnnulusRim) :
    ((sourceRimCoordinates phi theta F).symm z : X) =
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
        (hamiltonOneHierarchyCoordinates.symm (z.val, theta)) : X) := rfl

end PoincareMT.M76.HamiltonIntervalTorus
