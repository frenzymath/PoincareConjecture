import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.OneSheet.SurjectiveFundamentalGroup
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Isotopy.Mathlib.HomotopyFundamentalGroup

/-!
# Covering self-maps homotopic to the identity

The retained identity homotopy supplies the surjectivity used by the
one-sheet theorem, at the literal image of each basepoint. The basepoint
need not stay fixed during the homotopy.
-/

noncomputable section

namespace ContinuousMap.Homotopy

variable {X : Type*} [TopologicalSpace X] {f : C(X, X)}

/-- An identity homotopy makes the actual induced homomorphism surjective,
including when the basepoint moves. -/
theorem fundamentalGroup_map_surjective_of_id
    (F : (ContinuousMap.id X).Homotopy f) (x : X) :
    Function.Surjective (FundamentalGroup.map f x) := by
  let Frel : (ContinuousMap.id X).HomotopyRel f ∅ :=
    { F with prop' := by simp }
  exact (Frel.fundamentalGroup_map_bijective x).2

end ContinuousMap.Homotopy

namespace IsCoveringMap

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] {f : C(X, X)}

/-- A covering self-map homotopic to the identity is bijective. -/
theorem bijective_of_homotopy_id (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).Homotopy f) : Function.Bijective f := by
  let x : X := Classical.choice inferInstance
  exact hf.bijective_of_fundamentalGroup_map_surjective x
    (F.fundamentalGroup_map_surjective_of_id x)

/-- Turn the supplied covering self-map into a homeomorphism using only
its retained identity homotopy. -/
def homeomorphOfHomotopyId (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).Homotopy f) : X ≃ₜ X :=
  hf.isLocalHomeomorph.toHomeomorphOfBijective (hf.bijective_of_homotopy_id F)

@[simp] theorem homeomorphOfHomotopyId_apply (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).Homotopy f) (x : X) :
    hf.homeomorphOfHomotopyId F x = f x := rfl

/-- The original relative identity homotopy supplies the same exact-map
homeomorphism without an additional fundamental-group hypothesis. -/
def homeomorphOfHomotopyRelId {S : Set X} (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).HomotopyRel f S) : X ≃ₜ X :=
  hf.homeomorphOfHomotopyId F.toHomotopy

@[simp] theorem homeomorphOfHomotopyRelId_apply {S : Set X} (hf : IsCoveringMap f)
    (F : (ContinuousMap.id X).HomotopyRel f S) (x : X) :
    hf.homeomorphOfHomotopyRelId F x = f x := rfl

end IsCoveringMap
