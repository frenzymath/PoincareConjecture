import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonZeroPeriodLattice
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLowerPeriodLattice
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonLatticeHandleModel

/-!
# The original coordinates of the first two target hierarchy cuts

Only the actual period64 closed-torus and period512 interval-torus
consumers are used. Every representative, bounded coordinate and
old boundary marking is retained. See Waldhausen1968, pp.57--60,
Hamilton1976, pp.65--66, and rigidity050, sections3--5.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V0" => (Fin 0 → ℝ)
local notation "V1" => (Fin 1 → ℝ)
local notation "D0" => closedBall (0 : V0) 1
local notation "D1" => closedBall (0 : V1) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "H1" => LatticeHandle (Fin 1) (Fin 2) L1
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "C1" => AddCircle (4 * (128 : ℝ))

/-- Remove only the unique bounded coordinate from the original
closed three-torus. Its lattice and period remain fixed. See050. -/
noncomputable def hamiltonZeroHierarchyCoordinates : H0 ≃ₜ ((C0 × C0) × C0) where
  toFun z := hamiltonZeroLatticeProductEquiv z.2
  invFun z := (⟨0, mem_closedBall_self zero_le_one⟩,
    hamiltonZeroLatticeProductEquiv.symm z)
  left_inv z := Prod.ext (Subsingleton.elim _ _)
    (hamiltonZeroLatticeProductEquiv.symm_apply_apply z.2)
  right_inv z := hamiltonZeroLatticeProductEquiv.apply_symm_apply z
  continuous_toFun := hamiltonZeroLatticeProductEquiv.continuous.comp continuous_snd
  continuous_invFun := continuous_const.prodMk hamiltonZeroLatticeProductEquiv.symm.continuous

/-- Every original quotient representative has exactly its three
original circle coordinates. See rigidity050, section3. -/
theorem hamiltonZeroHierarchyCoordinates_mk (x : Fin 3 → ℝ) :
    hamiltonZeroHierarchyCoordinates
      (⟨0, mem_closedBall_self zero_le_one⟩, QuotientAddGroup.mk x) =
        (((x 0 : C0), (x 1 : C0)), (x 2 : C0)) := rfl

/-- Inverse product coordinates recover the original quotient
and its unique bounded-coordinate point. See rigidity050, section3. -/
theorem hamiltonZeroHierarchyCoordinates_symm_coe (s t u : ℝ) :
    hamiltonZeroHierarchyCoordinates.symm (((s : C0), (t : C0)), (u : C0)) =
      (⟨0, mem_closedBall_self zero_le_one⟩, QuotientAddGroup.mk ![s, t, u]) := by
  apply hamiltonZeroHierarchyCoordinates.injective
  rw [hamiltonZeroHierarchyCoordinates.apply_symm_apply,
    hamiltonZeroHierarchyCoordinates_mk]
  rfl

/-- The original closed zero handle has empty old boundary.
No boundary component is discarded by its coordinates. See050. -/
theorem hamiltonZeroHandleBoundary_eq_empty :
    latticeHandleBoundary (Fin 0) (Fin 3) L0 = ∅ := by
  ext z
  change (‖(z.1 : V0)‖ = 1 ∧ True) ↔ False
  have hz : (z.1 : V0) = 0 := Subsingleton.elim _ _
  rw [hz, norm_zero]
  norm_num

/-- Split the two original period512 circle coordinates while
retaining the entire original bounded interval. See050, section4. -/
noncomputable def hamiltonOneHierarchyCoordinates : H1 ≃ₜ ((D1 × C1) × C1) := by
  let q := hamiltonLowerLatticePiEquiv (Fin 2)
  refine {
    toFun := fun z => ((z.1, q z.2 0), q z.2 1)
    invFun := fun z => (z.1.1, q.symm ![z.1.2, z.2])
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_
  }
  · intro z
    change (z.1, q.symm ![q z.2 0, q z.2 1]) = z
    apply Prod.ext
    · rfl
    · apply q.injective
      rw [q.apply_symm_apply]
      funext i
      fin_cases i <;> rfl
  · intro z
    change ((z.1.1, q (q.symm ![z.1.2, z.2]) 0),
      q (q.symm ![z.1.2, z.2]) 1) = z
    rw [q.apply_symm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (continuous_fst.prodMk
      ((continuous_apply 0).comp (q.continuous.comp continuous_snd))).prodMk
        ((continuous_apply 1).comp (q.continuous.comp continuous_snd))
  · apply continuous_fst.fst.prodMk
    apply q.symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst.snd
    · exact continuous_snd

/-- The interval-torus coordinates use the literal old lattice
representative without a deck translation. See rigidity050, section4. -/
theorem hamiltonOneHierarchyCoordinates_mk (x : D1) (s t : ℝ) :
    hamiltonOneHierarchyCoordinates (x, QuotientAddGroup.mk ![s, t]) =
      ((x, (s : C1)), (t : C1)) := rfl

/-- Inverse coordinates retain both the original interval point
and the original quotient class. See rigidity050, section4. -/
theorem hamiltonOneHierarchyCoordinates_symm_coe (x : D1) (s t : ℝ) :
    hamiltonOneHierarchyCoordinates.symm ((x, (s : C1)), (t : C1)) =
      (x, QuotientAddGroup.mk ![s, t]) := by
  apply hamiltonOneHierarchyCoordinates.injective
  rw [hamiltonOneHierarchyCoordinates.apply_symm_apply,
    hamiltonOneHierarchyCoordinates_mk]

/-- The first target annulus retains the whole original norm-one
rim, before any cut is performed. See rigidity050, section4. -/
def hamiltonOneAnnulusRim : Set (D1 × C1) :=
  {z | ‖(z.1 : V1)‖ = 1}

/-- The actual coordinate change preserves the complete original
boundary equation, at every circle point. See rigidity050, section4. -/
theorem hamiltonOneHierarchyCoordinates_preimage_boundary :
    hamiltonOneHierarchyCoordinates ⁻¹'
      (hamiltonOneAnnulusRim ×ˢ (univ : Set C1)) =
        latticeHandleBoundary (Fin 1) (Fin 2) L1 := by
  ext z
  rfl

end PoincareMT.M76
