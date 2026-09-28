import PoincareConjecture.Proofs.M02.Topology.IntegralExcision









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSubspaceChains_homology_mono_of_contractible
    (A : Set X) [ContractibleSpace A] (n : Nat) :
    Mono (HomologicalComplex.homologyMap (integralSubspaceChains A) n) := by
  obtain ⟨a, ⟨H⟩⟩ := id_nullhomotopic A
  let i : TopCat.of A ⟶ TopCat.of X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let q : TopCat.of X ⟶ TopCat.of A := TopCat.ofHom (ContinuousMap.const X a)
  let HT : TopCat.Homotopy (𝟙 (TopCat.of A)) (i ≫ q) := H
  have he := HT.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
  change HomologicalComplex.homologyMap (integralChainsFunctor.map (𝟙 _)) n =
    HomologicalComplex.homologyMap (integralChainsFunctor.map (i ≫ q)) n at he
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    CategoryTheory.Functor.map_comp, HomologicalComplex.homologyMap_comp] at he
  exact mono_of_mono_fac he.symm


theorem integralToRelativeHomology_isIso_of_contractible
    (A : Set X) [ContractibleSpace A] (n : Nat) :
    IsIso (integralToRelativeHomology A (n + 1)) := by
  let S := integralPairSequence_shortExact A
  have hA := integral_contractible_homology_isZero A (n + 1) (by omega)
  let : Mono (integralToRelativeHomology A (n + 1)) :=
    (S.homology_exact₂ (n + 1)).mono_g (hA.eq_of_src _ _)
  let : Mono (HomologicalComplex.homologyMap (integralSubspaceChains A) n) :=
    integralSubspaceChains_homology_mono_of_contractible A n
  have hδ : S.δ (n + 1) n rfl = 0 := by
    apply (cancel_mono (HomologicalComplex.homologyMap (integralSubspaceChains A) n)).mp
    exact (S.δ_comp (n + 1) n rfl).trans zero_comp.symm
  let : Epi (integralToRelativeHomology A (n + 1)) :=
    (S.homology_exact₃ (n + 1) n rfl).epi_f hδ
  exact isIso_of_mono_of_epi _


def integralContractibleCoverHomologyIso
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) (n : Nat) :
    integralHomology X (n + 2) ≅
      integralHomology ((Subtype.val : B → X) ⁻¹' A) (n + 1) := by
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let e := integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := AB) (B := A) (fun _ hb => hb)
  let : IsIso (integralToRelativeHomology A (n + 2)) :=
    integralToRelativeHomology_isIso_of_contractible A (n + 1)
  let : IsIso (HomologicalComplex.homologyMap e (n + 2)) :=
    integral_open_cover_excision A B hA hB hcover (n + 2)
  exact asIso (integralToRelativeHomology A (n + 2)) ≪≫
    (asIso (HomologicalComplex.homologyMap e (n + 2))).symm ≪≫
    (integralPairSequence_shortExact AB).δIso (n + 2) (n + 1) rfl
      (integral_contractible_homology_isZero B (n + 2) (by omega))
      (integral_contractible_homology_isZero B (n + 1) (by omega))



def integralContractibleCoverHomologyOneIso
    (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    integralHomology X 1 ≅ kernel (HomologicalComplex.homologyMap
      (integralSubspaceChains ((Subtype.val : B → X) ⁻¹' A)) 0) := by
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  let e := integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := AB) (B := A) (fun _ hb => hb)
  let : IsIso (integralToRelativeHomology A 1) :=
    integralToRelativeHomology_isIso_of_contractible A 0
  let : IsIso (HomologicalComplex.homologyMap e 1) :=
    integral_open_cover_excision A B hA hB hcover 1
  let S := integralPairSequence_shortExact AB
  let : Mono (S.δ 1 0 rfl) :=
    S.mono_δ 1 0 rfl (integral_contractible_homology_isZero B 1 (by omega))
  exact asIso (integralToRelativeHomology A 1) ≪≫
    (asIso (HomologicalComplex.homologyMap e 1)).symm ≪≫
    (S.homology_exact₁ 1 0 rfl).fIsKernel.conePointUniqueUpToIso (limit.isLimit _)

end PoincareConjecture.Proofs.M02.Topology
