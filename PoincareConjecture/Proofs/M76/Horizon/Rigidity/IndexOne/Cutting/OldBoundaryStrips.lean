import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.SourceSlab

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

noncomputable def oldSlabCoordinates (phi : C(H, H)) (a b : ℝ)
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ↥(sourceSlab phi a b ∩ frontier R) ≃ₜ
      (hamiltonOneAnnulusRim × AddCircle.closedIntervalArc p a b) := by
  let E := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  have hB (x : R) : E x ∈ B ↔ (x : X) ∈ frontier R :=
    Set.ext_iff.mp (latticeHandleDomainEquiv_preimage_boundary (Fin 1) (Fin 2) L) x
  let f : ↥(sourceSlab phi a b ∩ frontier R) →
      (hamiltonOneAnnulusRim × AddCircle.closedIntervalArc p a b) := fun z => by
    let x : R := ⟨z.val, sourceSlab_subset phi a b z.property.1⟩
    have hxB := (hB x).mpr z.property.2
    refine (⟨(hamiltonOneHierarchyCoordinates (E x)).1, hxB.1⟩,
      ⟨(hamiltonOneHierarchyCoordinates (E x)).2, ?_⟩)
    rw [← sourcePhase_eq_on_boundary phi F (E x) hxB]
    exact (mem_sourceSlab_iff phi a b x).mp z.property.1
  let g : (hamiltonOneAnnulusRim × AddCircle.closedIntervalArc p a b) →
      ↥(sourceSlab phi a b ∩ frontier R) := fun z => by
    let x := hamiltonOneHierarchyCoordinates.symm (z.1.val, z.2.val)
    have hxB : x ∈ B := ⟨z.1.property, mem_univ _⟩
    have hxphase : sourcePhase phi x = z.2.val := by
      rw [sourcePhase_eq_on_boundary phi F x hxB]
      exact congrArg Prod.snd (hamiltonOneHierarchyCoordinates.apply_symm_apply _)
    refine ⟨E.symm x, ?_, ?_⟩
    · apply (mem_sourceSlab_iff phi a b (E.symm x)).mpr
      rw [E.apply_symm_apply, hxphase]
      exact z.2.property
    · apply (hB (E.symm x)).mp
      simpa only [E.apply_symm_apply] using hxB
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_
  }
  · intro z
    apply Subtype.ext
    change (E.symm (hamiltonOneHierarchyCoordinates.symm
      ((hamiltonOneHierarchyCoordinates (E ⟨z.val, sourceSlab_subset phi a b z.property.1⟩)).1,
        (hamiltonOneHierarchyCoordinates (E ⟨z.val, sourceSlab_subset phi a b z.property.1⟩)).2)) : X) = z.val
    rw [Prod.eta, hamiltonOneHierarchyCoordinates.symm_apply_apply, E.symm_apply_apply]
  · intro z
    apply Prod.ext <;> apply Subtype.ext
    · change (hamiltonOneHierarchyCoordinates
        (E (E.symm (hamiltonOneHierarchyCoordinates.symm (z.1.val, z.2.val))))).1 = z.1.val
      rw [E.apply_symm_apply, hamiltonOneHierarchyCoordinates.apply_symm_apply]
    · change (hamiltonOneHierarchyCoordinates
        (E (E.symm (hamiltonOneHierarchyCoordinates.symm (z.1.val, z.2.val))))).2 = z.2.val
      rw [E.apply_symm_apply, hamiltonOneHierarchyCoordinates.apply_symm_apply]
  · apply Continuous.prodMk
    · apply Continuous.subtype_mk
      change Continuous (fun z : ↥(sourceSlab phi a b ∩ frontier R) =>
        (hamiltonOneHierarchyCoordinates
          (E ⟨z.val, sourceSlab_subset phi a b z.property.1⟩)).1)
      fun_prop
    · apply Continuous.subtype_mk
      change Continuous (fun z : ↥(sourceSlab phi a b ∩ frontier R) =>
        (hamiltonOneHierarchyCoordinates
          (E ⟨z.val, sourceSlab_subset phi a b z.property.1⟩)).2)
      fun_prop
  · apply Continuous.subtype_mk
    change Continuous (fun z : (hamiltonOneAnnulusRim × AddCircle.closedIntervalArc p a b) =>
      (E.symm (hamiltonOneHierarchyCoordinates.symm (z.1.val, z.2.val)) : X))
    fun_prop

theorem oldSlabCoordinates_symm_original_point (phi : C(H, H)) (a b : ℝ)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (z : hamiltonOneAnnulusRim × AddCircle.closedIntervalArc p a b) :
    ((oldSlabCoordinates phi a b F).symm z : X) =
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
        (hamiltonOneHierarchyCoordinates.symm (z.1.val, z.2.val)) : X) := rfl

noncomputable def closedPhaseIntervalCoordinates (a b : ℝ) (ha : 0 ≤ a) (hb : b < p) :
    Icc a b ≃ₜ AddCircle.closedIntervalArc p a b := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hinj : InjOn (fun t : ℝ => (t : C)) (Icc a b) := by
    intro x hx y hy hxy
    have hxI : x ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith [hx.1, hx.2]
    have hyI : y ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith [hy.1, hy.2]
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hxI hyI).mp hxy
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn (fun t : ℝ => (t : C)) (Icc a b) hinj)
    (((AddCircle.continuous_mk' p).comp continuous_subtype_val).subtype_mk _)

noncomputable def oldSlabIntervalCoordinates (phi : C(H, H)) (a b : ℝ)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (ha : 0 ≤ a) (hb : b < p) :
    ↥(sourceSlab phi a b ∩ frontier R) ≃ₜ (hamiltonOneAnnulusRim × Icc a b) :=
  (oldSlabCoordinates phi a b F).trans
    (Homeomorph.prodCongr (Homeomorph.refl _) (closedPhaseIntervalCoordinates a b ha hb).symm)

theorem oldSlabIntervalCoordinates_symm_original_point (phi : C(H, H)) (a b : ℝ)
    (F : (ContinuousMap.id H).HomotopyRel phi B) (ha : 0 ≤ a) (hb : b < p)
    (z : hamiltonOneAnnulusRim × Icc a b) :
    ((oldSlabIntervalCoordinates phi a b F ha hb).symm z : X) =
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm
        (hamiltonOneHierarchyCoordinates.symm (z.1.val, ((z.2 : ℝ) : C))) : X) := rfl

end PoincareConjecture.M76.HamiltonIntervalTorus
