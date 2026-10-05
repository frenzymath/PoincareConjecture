import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralAmbientRelative

/-!
# Naturality of the boundary map for a pair

The boundary is the connecting map of the actual relative singular chain
sequence. Its naturality transports the sphere reflection sign to local
homology, as in Hatcher, Section 3.3, p. 233.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set

universe u

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Restricting a map of pairs to their subspaces.
Source: Hatcher, Section 2.1, relative homology. -/
def pairSubspaceMap (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The relative connecting map commutes with a continuous map of pairs.
Source: Hatcher, Section 2.1, naturality of the pair sequence. -/
@[reassoc]
theorem integralRelativeBoundary_naturality
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (n : Nat) :
    homologyMap (integralRelativeMap f hf) (n + 1) ≫ integralRelativeBoundary B n =
      integralRelativeBoundary A n ≫
        homologyMap (integralChainsFunctor.map (TopCat.ofHom (pairSubspaceMap f hf))) n := by
  let F : integralPairSequence A ⟶ integralPairSequence B :=
    { τ₁ := integralChainsFunctor.map (TopCat.ofHom (pairSubspaceMap f hf))
      τ₂ := integralChainsFunctor.map (TopCat.ofHom f)
      τ₃ := integralRelativeMap f hf
      comm₁₂ := by
        dsimp only [integralPairSequence, ShortComplex.cokernelSequence,
          integralSubspaceChains]
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl
      comm₂₃ := (integralRelativeMap_projection f hf).symm }
  exact (HomologySequence.δ_naturality F (integralPairSequence_shortExact A)
    (integralPairSequence_shortExact B) (n + 1) n rfl).symm

/-- On a contractible ambient space, the relative boundary detects maps in
positive degrees. Source: Hatcher, Section 3.3, p. 233. -/
theorem integralRelativeBoundary_isIso [ContractibleSpace X] (A : Set X) (n : Nat) :
    IsIso (integralRelativeBoundary A (n + 1)) := by
  change IsIso (integralContractibleAmbientRelativeBoundaryIso A n).hom
  infer_instance

end Poincare.Topology.Orientation.ProjectivePlane
