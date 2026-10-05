import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.SphereUnionInvariant
import PoincareLib.Topology.Manifold.Surgery.Reduction.Statement

/-!
# Finite connected-sum induction

Step preservation of the finite sphere-union invariant propagates through
the genuine reflexive-transitive connected-sum relation. Connectedness is
used only at the final carrier to recover one standard sphere. These
conditional helpers follow Morgan--Tian Corollary 15.4, pp. 358-359;
see `proof-work/tasks/M74/derivations/finite-induction.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT
namespace M74

/-- Preservation under each genuine connected-sum operation propagates
the sphere-union invariant along a finite sequence, including the empty
sequence. Source: Morgan--Tian Corollary 15.4, pp. 358-359. -/
theorem SphereUnion.of_reflTransGen
    (hstep : ∀ A C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumStep A C → SphereUnion A → SphereUnion C)
    {A C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) (hA : SphereUnion A) :
    SphereUnion C := by
  induction h with
  | refl => exact hA
  | tail _ hnext ih => exact hstep _ _ hnext ih

/-- An assembly of sphere factors has a sphere-union target whenever one
connected-sum operation preserves that invariant. Source: the finite
induction in Morgan--Tian Corollary 15.4, pp. 358-359. -/
theorem SphereUnion.of_assembly
    (hstep : ∀ A C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumStep A C → SphereUnion A → SphereUnion C)
    {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}} (A : SmoothFiniteConnectedSumAssembly pieces C)
    (hpieces : ∀ i,
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) (pieces i).carrier ThreeSphere ∞)) :
    SphereUnion C :=
  SphereUnion.of_reflTransGen hstep A.operations (SphereUnion.initial A hpieces)

/-- The frozen M74 reduction follows from preservation of finite sphere
unions by genuine connected-sum operations. The preservation premise is
an explicit obligation of this helper. Source: Morgan--Tian Corollary
15.4(2), pp. 358-359; see `derivations/finite-induction.md`. -/
theorem connectedSumReduction_of_preserves_sphereUnion
    (hstep : ∀ A C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumStep A C → SphereUnion A → SphereUnion C) :
    M74ConnectedSumReductionStatement.{u} := by
  intro n pieces C I
  refine ⟨⟨?_⟩⟩
  exact SphereUnion.nonempty_diffeomorph_threeSphere
    (SphereUnion.of_assembly hstep I.assembly I.factor_sphere) I.target_connected

end M74
end PoincareMT
