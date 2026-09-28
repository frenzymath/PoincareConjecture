import PoincareConjecture.Proofs.M74.Cor15_4.SphereUnionInvariant
import PoincareConjecture.Statements.M74ConnectedSumReduction

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture
namespace M74

theorem SphereUnion.of_reflTransGen
    (hstep : ∀ A C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumStep A C → SphereUnion A → SphereUnion C)
    {A C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) (hA : SphereUnion A) :
    SphereUnion C := by
  induction h with
  | refl => exact hA
  | tail _ hnext ih => exact hstep _ _ hnext ih

theorem SphereUnion.of_assembly
    (hstep : ∀ A C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumStep A C → SphereUnion A → SphereUnion C)
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (A : SmoothFiniteConnectedSumAssembly pieces C)
    (hpieces : ∀ i,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)) :
    SphereUnion C :=
  SphereUnion.of_reflTransGen hstep A.operations (SphereUnion.initial A hpieces)

theorem connectedSumReduction_of_preserves_sphereUnion
    (hstep : ∀ A C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumStep A C → SphereUnion A → SphereUnion C) :
    M74ConnectedSumReductionStatement.{u} := by
  intro n pieces C I
  refine ⟨⟨?_⟩⟩
  exact SphereUnion.nonempty_diffeomorph_threeSphere
    (SphereUnion.of_assembly hstep I.assembly I.factor_sphere) I.target_connected

end M74
end PoincareConjecture
