import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.LatticeRigidity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.General.IndexTwoRigidity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.General.IndexZeroRigidity



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

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

end PoincareConjecture.M76
