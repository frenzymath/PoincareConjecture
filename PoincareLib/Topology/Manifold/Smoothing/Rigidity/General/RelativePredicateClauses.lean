import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.LatticeRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.IndexTwoRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.IndexZeroRigidity

/-! Exact nonzero-index clauses of the unchanged Hamilton predicate. -/

set_option autoImplicit false
open Set

namespace PoincareMT.M76

theorem hasHamiltonRelativeTorusRigidity_of_card_one_two
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    (Λ : Submodule ℤ (κ → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hι : Fintype.card ι = 1) (hκ : Fintype.card κ = 2)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ)) :
    HasHamiltonRelativeTorusRigidity ι κ Λ e d := by
  intro _ _ hd hI hJ phi hphi hproper hhom
  obtain ⟨F⟩ := hhom
  exact exists_indexOne_lattice_rigidity Λ e d hι hκ hd hI hJ phi hphi hproper F

theorem hasHamiltonRelativeTorusRigidity_of_card_two_one
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    (Λ : Submodule ℤ (κ → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hι : Fintype.card ι = 2) (hκ : Fintype.card κ = 1)
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ)) :
    HasHamiltonRelativeTorusRigidity ι κ Λ e d := by
  intro _ _ hd hI hJ phi hphi hproper hhom
  obtain ⟨F⟩ := hhom
  exact exists_indexTwo_lattice_rigidity Λ e d hι hκ hd hI hJ phi hphi hproper F

/-- Hamilton relative rigidity from the unchanged original premises, for all
coordinate types, lattices, and source and target chart families. -/
theorem hasHamiltonRelativeTorusRigidity
    {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    (Λ : Submodule ℤ (κ → ℝ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ))
    (d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ Λ) (Fin 3 → ℝ)) :
    HasHamiltonRelativeTorusRigidity ι κ Λ e d := by
  intro hcard hlower
  have hcases : Fintype.card ι = 0 ∨ Fintype.card ι = 1 ∨ Fintype.card ι = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · exact hasHamiltonRelativeTorusRigidity_of_card_zero_three Λ hzero
      (by omega) e d hcard hlower
  · exact hasHamiltonRelativeTorusRigidity_of_card_one_two Λ hone
      (by omega) e d hcard hlower
  · exact hasHamiltonRelativeTorusRigidity_of_card_two_one Λ htwo
      (by omega) e d hcard hlower

/-! The lower-handle consumer needs all three specialized rigidity families.
Once the index-zero family is constructed, the two nonzero families are the
checked clauses above and can be assembled without changing the frozen
predicate or adding a supplier premise. -/
theorem lowerRigidityFamily_of_index_zero
    (hzero :
      ∀ (charts : Set (OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
          (Fin 3 → ℝ)))
        (d : ((Fin 0 → ℝ) × (Fin 3 → ℝ)) →
          OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
            (Fin 3 → ℝ)),
        HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3)
          hamiltonZeroPeriodLattice
          (fun c : charts => (c : OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
            (Fin 3 → ℝ))) d) :
      (∀ (charts : Set (OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
          (Fin 3 → ℝ)))
        (d : ((Fin 0 → ℝ) × (Fin 3 → ℝ)) →
          OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
            (Fin 3 → ℝ)),
        HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3)
          hamiltonZeroPeriodLattice
          (fun c : charts => (c : OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
            (Fin 3 → ℝ))) d) ∧
      (∀ (charts : Set (OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 1) (Fin 2)
            (hamiltonLowerPeriodLattice (Fin 2))) (Fin 3 → ℝ)))
        (d : ((Fin 1 → ℝ) × (Fin 2 → ℝ)) →
          OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 1) (Fin 2)
              (hamiltonLowerPeriodLattice (Fin 2))) (Fin 3 → ℝ)),
        HasHamiltonRelativeTorusRigidity (Fin 1) (Fin 2)
          (hamiltonLowerPeriodLattice (Fin 2))
          (fun c : charts => (c : OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 1) (Fin 2)
              (hamiltonLowerPeriodLattice (Fin 2))) (Fin 3 → ℝ))) d) ∧
      (∀ (charts : Set (OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 2) (Fin 1)
            (hamiltonLowerPeriodLattice (Fin 1))) (Fin 3 → ℝ)))
        (d : ((Fin 2 → ℝ) × (Fin 1 → ℝ)) →
          OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 2) (Fin 1)
              (hamiltonLowerPeriodLattice (Fin 1))) (Fin 3 → ℝ)),
        HasHamiltonRelativeTorusRigidity (Fin 2) (Fin 1)
          (hamiltonLowerPeriodLattice (Fin 1))
          (fun c : charts => (c : OpenPartialHomeomorph
            (LatticeHandleAmbient (Fin 2) (Fin 1)
              (hamiltonLowerPeriodLattice (Fin 1))) (Fin 3 → ℝ))) d) := by
  refine ⟨hzero, ?_, ?_⟩
  · intro charts d
    exact hasHamiltonRelativeTorusRigidity_of_card_one_two
      (hamiltonLowerPeriodLattice (Fin 2)) (by simp) (by simp)
      (fun c : charts => (c : OpenPartialHomeomorph
        (LatticeHandleAmbient (Fin 1) (Fin 2)
          (hamiltonLowerPeriodLattice (Fin 2))) (Fin 3 → ℝ))) d
  · intro charts d
    exact hasHamiltonRelativeTorusRigidity_of_card_two_one
      (hamiltonLowerPeriodLattice (Fin 1)) (by simp) (by simp)
      (fun c : charts => (c : OpenPartialHomeomorph
        (LatticeHandleAmbient (Fin 2) (Fin 1)
          (hamiltonLowerPeriodLattice (Fin 1))) (Fin 3 → ℝ))) d

/-! The lower-handle chain can now consume the constructed zero-index clause
without retaining a producer premise. -/
theorem lowerRigidityFamily_of_constructed_index_zero :
    (∀ (charts : Set (OpenPartialHomeomorph
        (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
        (Fin 3 → ℝ)))
      (d : ((Fin 0 → ℝ) × (Fin 3 → ℝ)) →
        OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
          (Fin 3 → ℝ)),
      HasHamiltonRelativeTorusRigidity (Fin 0) (Fin 3)
        hamiltonZeroPeriodLattice
        (fun c : charts => (c : OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice)
          (Fin 3 → ℝ))) d) ∧
    (∀ (charts : Set (OpenPartialHomeomorph
        (LatticeHandleAmbient (Fin 1) (Fin 2)
          (hamiltonLowerPeriodLattice (Fin 2))) (Fin 3 → ℝ)))
      (d : ((Fin 1 → ℝ) × (Fin 2 → ℝ)) →
        OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 1) (Fin 2)
            (hamiltonLowerPeriodLattice (Fin 2))) (Fin 3 → ℝ)),
      HasHamiltonRelativeTorusRigidity (Fin 1) (Fin 2)
        (hamiltonLowerPeriodLattice (Fin 2))
        (fun c : charts => (c : OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 1) (Fin 2)
            (hamiltonLowerPeriodLattice (Fin 2))) (Fin 3 → ℝ))) d) ∧
    (∀ (charts : Set (OpenPartialHomeomorph
        (LatticeHandleAmbient (Fin 2) (Fin 1)
          (hamiltonLowerPeriodLattice (Fin 1))) (Fin 3 → ℝ)))
      (d : ((Fin 2 → ℝ) × (Fin 1 → ℝ)) →
        OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 2) (Fin 1)
            (hamiltonLowerPeriodLattice (Fin 1))) (Fin 3 → ℝ)),
      HasHamiltonRelativeTorusRigidity (Fin 2) (Fin 1)
        (hamiltonLowerPeriodLattice (Fin 1))
        (fun c : charts => (c : OpenPartialHomeomorph
          (LatticeHandleAmbient (Fin 2) (Fin 1)
            (hamiltonLowerPeriodLattice (Fin 1))) (Fin 3 → ℝ))) d) := by
  exact lowerRigidityFamily_of_index_zero
    (fun charts d => hasHamiltonRelativeTorusRigidity_zero charts d)

end PoincareMT.M76
