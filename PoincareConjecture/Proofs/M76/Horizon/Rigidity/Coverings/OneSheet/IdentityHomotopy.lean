import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.OneSheet.SurjectiveFundamentalGroup
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup

noncomputable section

namespace ContinuousMap.Homotopy

variable {X : Type*} [TopologicalSpace X] {f : C(X, X)}

theorem fundamentalGroup_map_surjective_of_id
    (F : (ContinuousMap.id X).Homotopy f) (x : X) :
    Function.Surjective (FundamentalGroup.map f x) := by
  let Frel : (ContinuousMap.id X).HomotopyRel f ∅ :=
    { F with prop' := by simp }
  exact (Frel.fundamentalGroup_map_bijective x).2

end ContinuousMap.Homotopy

namespace IsCoveringMap

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] {f : C(X, X)}

theorem bijective_of_homotopy_id (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).Homotopy f) : Function.Bijective f := by
  let x : X := Classical.choice inferInstance
  exact hf.bijective_of_fundamentalGroup_map_surjective x
    (F.fundamentalGroup_map_surjective_of_id x)

def homeomorphOfHomotopyId (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).Homotopy f) : X ≃ₜ X :=
  hf.isLocalHomeomorph.toHomeomorphOfBijective (hf.bijective_of_homotopy_id F)

@[simp] theorem homeomorphOfHomotopyId_apply (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).Homotopy f) (x : X) :
    hf.homeomorphOfHomotopyId F x = f x := rfl

def homeomorphOfHomotopyRelId {S : Set X} (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).HomotopyRel f S) : X ≃ₜ X :=
  hf.homeomorphOfHomotopyId F.toHomotopy

@[simp] theorem homeomorphOfHomotopyRelId_apply {S : Set X} (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).HomotopyRel f S) (x : X) :
    hf.homeomorphOfHomotopyRelId F x = f x := rfl

end IsCoveringMap
