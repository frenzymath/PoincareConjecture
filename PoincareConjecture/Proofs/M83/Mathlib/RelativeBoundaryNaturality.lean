import PoincareConjecture.Proofs.M02.Topology.IntegralAmbientRelative









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set

universe u

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]



def pairSubspaceMap (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x, hf x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩



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



theorem integralRelativeBoundary_isIso [ContractibleSpace X] (A : Set X) (n : Nat) :
    IsIso (integralRelativeBoundary A (n + 1)) := by
  change IsIso (integralContractibleAmbientRelativeBoundaryIso A n).hom
  infer_instance

end PoincareConjecture.Proofs.M83
