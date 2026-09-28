import PoincareConjecture.Proofs.M02.Topology.IntegralSmallHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] {I : Type v}

private theorem integralSubspaceChains_small (U : I → Set X) (A : Set X)
    (n : Nat) (c : (integralChains A).X n)
    (hc : c ∈ integralSmallChains (fun i => (Subtype.val : A → X) ⁻¹' U i) n) :
    (integralSubspaceChains A).f n c ∈ integralSmallChains U n := by
  let V : I → Set A := fun i => (Subtype.val : A → X) ⁻¹' U i
  have hle : integralSmallChains V n ≤
      (integralSmallChains U n).comap ((integralSubspaceChains A).f n).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have he := congrArg (fun q => q (ULift.up 1)) (integralSingularGenerator_map s.val v)
    change (integralSubspaceChains A).f n (integralSingularGenerator s.val (ULift.up 1)) =
      integralSingularGenerator (v.comp s.val) (ULift.up 1) at he
    change (integralSubspaceChains A).f n (integralSingularGenerator s.val (ULift.up 1))
      ∈ integralSmallChains U n
    rw [he]
    apply Submodule.subset_span
    refine ⟨⟨v.comp s.val, ?_⟩, rfl⟩
    obtain ⟨i, hi⟩ := s.property
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨z, rfl⟩
  exact hle hc

def integralSmallSubspaceChains (U : I → Set X) (A : Set X) :
    integralSmallChainComplex (fun i => (Subtype.val : A → X) ⁻¹' U i) ⟶
      integralSmallChainComplex U where
  f n := by
    let V : I → Set A := fun i => (Subtype.val : A → X) ⁻¹' U i
    letI : Module Int (integralSmallChains V n) := (integralSmallChains V n).module
    letI : Module Int (integralSmallChains U n) := (integralSmallChains U n).module
    exact ModuleCat.ofHom (LinearMap.codRestrict (integralSmallChains U n)
      (((integralSubspaceChains A).f n).hom.domRestrict (integralSmallChains V n))
      (fun c => integralSubspaceChains_small U A n c.val c.property))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun q => q c.val) ((integralSubspaceChains A).comm i j)

theorem integralSmallSubspaceChains_inclusion (U : I → Set X) (A : Set X) :
    integralSmallSubspaceChains U A ≫ integralSmallChainInclusion U =
      integralSmallChainInclusion (fun i => (Subtype.val : A → X) ⁻¹' U i) ≫
        integralSubspaceChains A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

theorem integralSmallSubspaceChains_mono (U : I → Set X) (A : Set X) :
    Mono (integralSmallSubspaceChains U A) := by
  let : Mono (integralSubspaceChains A) := integralSubspaceChains_mono A
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b h
  apply Subtype.ext
  apply (ModuleCat.mono_iff_injective ((integralSubspaceChains A).f n)).mp inferInstance
  exact congrArg Subtype.val h

abbrev integralSmallRelativeChains (U : I → Set X) (A : Set X) :
    ChainComplex (ModuleCat.{u} Int) Nat :=
  cokernel (integralSmallSubspaceChains U A)

abbrev integralSmallRelativeProjection (U : I → Set X) (A : Set X) :
    integralSmallChainComplex U ⟶ integralSmallRelativeChains U A :=
  cokernel.π (integralSmallSubspaceChains U A)

def integralSmallRelativeComparison (U : I → Set X) (A : Set X) :
    integralSmallRelativeChains U A ⟶ integralRelativeChains A :=
  cokernel.map (integralSmallSubspaceChains U A) (integralSubspaceChains A)
    (integralSmallChainInclusion (fun i => (Subtype.val : A → X) ⁻¹' U i))
    (integralSmallChainInclusion U) (integralSmallSubspaceChains_inclusion U A)

theorem integralSmallRelativeComparison_projection (U : I → Set X) (A : Set X) :
    integralSmallRelativeProjection U A ≫ integralSmallRelativeComparison U A =
      integralSmallChainInclusion U ≫ integralRelativeProjection A :=
  cokernel.π_desc _ _ _

theorem integralSmallRelativeComparison_quasiIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (A : Set X) :
    QuasiIso (integralSmallRelativeComparison U A) := by
  let V : I → Set A := fun i => (Subtype.val : A → X) ⁻¹' U i
  have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage continuous_subtype_val
  have hcoverV : (⋃ i, V i) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro a
    have ha : a.val ∈ ⋃ i, U i := by rw [hcover]; exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  let S := ShortComplex.cokernelSequence (integralSmallSubspaceChains U A)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := integralSmallSubspaceChains_mono U A }
  let φ : S ⟶ integralPairSequence A :=
    { τ₁ := integralSmallChainInclusion V
      τ₂ := integralSmallChainInclusion U
      τ₃ := integralSmallRelativeComparison U A
      comm₁₂ := integralSmallSubspaceChains_inclusion U A
      comm₂₃ := (integralSmallRelativeComparison_projection U A).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS
    (integralPairSequence_shortExact A)
    (integralSmallChainInclusion_quasiIso V hV hcoverV)
    (integralSmallChainInclusion_quasiIso U hU hcover)

theorem integralSmallRelativeComparison_homology_isIso
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (A : Set X) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap (integralSmallRelativeComparison U A) n) := by
  let := integralSmallRelativeComparison_quasiIso U hU hcover A
  infer_instance

end PoincareConjecture.Proofs.M02.Topology
