import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralRelativeChains
import Mathlib.LinearAlgebra.Finsupp.LSum









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial BigOperators

universe u

namespace Poincare.Topology

abbrev integralSimplex (n : Nat) := stdSimplex Real (Fin (n + 1))

def integralSimplexFace (n : Nat) (i : Fin (n + 2)) :
    C(integralSimplex n, integralSimplex (n + 1)) :=
  ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def integralSingularGenerator {n : Nat} (s : C(integralSimplex n, X)) :
    integralCoefficient.{u} ⟶ (integralChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s)

def integralChainCoordinates (X : Type u) [TopologicalSpace X] (n : Nat) :
    (integralChains X).X n ≃ₗ[Int]
      (C(integralSimplex n, X) →₀ ULift.{u} Int) :=
  let S := TopCat.toSSet.obj (TopCat.of X)
  let e := (S.isColimitChainComplexXCofan integralCoefficient n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (S.obj (Opposite.op ⦋n⦌)))
  e.toLinearEquiv.trans
    (Finsupp.domLCongr ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)))

theorem integralChainCoordinates_generator {n : Nat}
    (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
    integralChainCoordinates X n (integralSingularGenerator s a) = Finsupp.single s a := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let E := (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)
  let e := (S.isColimitChainComplexXCofan integralCoefficient n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (S.obj (Opposite.op ⦋n⦌)))
  have hι := IsColimit.comp_coconePointUniqueUpToIso_hom
    (S.isColimitChainComplexXCofan integralCoefficient n)
    (ModuleCat.finsuppCoconeIsColimit Int (ULift.{u} Int) (S.obj (Opposite.op ⦋n⦌)))
    (Discrete.mk (E.symm s))
  have he : e.hom (integralSingularGenerator s a) = Finsupp.single (E.symm s) a :=
    congrArg (fun f => f a) hι
  change Finsupp.domLCongr (R := Int) (M := ULift.{u} Int) E
    (e.hom (integralSingularGenerator s a)) = Finsupp.single s a
  rw [he, Finsupp.domLCongr_single, E.apply_symm_apply]

theorem integralSingularGenerator_boundary {n : Nat}
    (s : C(integralSimplex (n + 1), X)) :
    integralSingularGenerator s ≫ (integralChains X).d (n + 1) n =
      ∑ i : Fin (n + 2), ((-1 : Int) ^ i.val) •
        integralSingularGenerator (s.comp (integralSimplexFace n i)) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let E := (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)
  let E' := (TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n + 1⦌)
  change S.ιChainComplex (E'.symm s) ≫ (S.chainComplex integralCoefficient).d (n + 1) n =
    ∑ i : Fin (n + 2), ((-1 : Int) ^ i.val) •
      S.ιChainComplex (E.symm (s.comp (integralSimplexFace n i)))
  rw [SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : S.obj (Opposite.op ⦋n⦌) =>
    ((-1 : Int) ^ i.val) • S.ιChainComplex (R := integralCoefficient) x)
  apply E.injective
  ext z
  change (TopCat.of X).toSSetObjEquiv _ (S.δ i (E'.symm s)) z =
    (E (E.symm (s.comp (integralSimplexFace n i)))) z
  rw [TopCat.toSSetObjEquiv_δ_apply, E'.apply_symm_apply, E.apply_symm_apply]
  rfl

theorem integralSingularGenerator_map {n : Nat}
    (s : C(integralSimplex n, X)) (f : C(X, Y)) :
    integralSingularGenerator s ≫
      (integralChainsFunctor.map (TopCat.ofHom f)).f n =
        integralSingularGenerator (f.comp s) := by
  change (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) integralCoefficient).f n =
    (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
      (((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm (f.comp s))
  rw [SSet.ι_chainComplexMap_f]
  rfl

theorem integral_subspace_range_iff (A : Set X) (n : Nat)
    (c : (integralChains X).X n) :
    c ∈ LinearMap.range ((integralSubspaceChains A).f n).hom ↔
      ∀ s ∈ (integralChainCoordinates X n c).support, Set.range s ⊆ A := by
  classical
  let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(integralSimplex n, A) → C(integralSimplex n, X) := fun s => v.comp s
  let i := (integralSubspaceChains A).f n
  let EA := integralChainCoordinates A n
  let EX := integralChainCoordinates X n
  have hf : Function.Injective f := by
    intro s t h
    ext z
    exact congrArg (fun k : C(integralSimplex n, X) => k z) h
  have hgen (s : C(integralSimplex n, A)) :
      integralSingularGenerator s ≫ i = integralSingularGenerator (f s) :=
    integralSingularGenerator_map s v
  have hcoord : EX.toLinearMap.comp (i.hom.comp EA.symm.toLinearMap) =
      Finsupp.lmapDomain (ULift.{u} Int) Int f := by
    apply Finsupp.lhom_ext
    intro s a
    change EX (i (EA.symm (Finsupp.single s a))) =
      Finsupp.mapDomain f (Finsupp.single s a)
    have hs : EA.symm (Finsupp.single s a) = integralSingularGenerator s a := by
      apply EA.injective
      rw [EA.apply_symm_apply]
      exact (integralChainCoordinates_generator s a).symm
    have hg : i (integralSingularGenerator s a) = integralSingularGenerator (f s) a :=
      congrArg (fun k => k a) (hgen s)
    rw [hs, hg, integralChainCoordinates_generator, Finsupp.mapDomain_single]
  have happ (a : (integralChains A).X n) :
      EX (i a) = Finsupp.mapDomain f (EA a) := by
    have h := LinearMap.congr_fun hcoord (EA a)
    change EX (i (EA.symm (EA a))) = Finsupp.mapDomain f (EA a) at h
    simpa only [EA.symm_apply_apply] using h
  have hfrange (s : C(integralSimplex n, X)) :
      s ∈ Set.range f ↔ Set.range s ⊆ A := by
    constructor
    · rintro ⟨t, rfl⟩ y ⟨z, rfl⟩
      exact (t z).property
    · intro hs
      refine ⟨⟨fun z => ⟨s z, hs ⟨z, rfl⟩⟩, s.continuous.subtype_mk _⟩, ?_⟩
      ext z
      rfl
  have hrange : c ∈ LinearMap.range i.hom ↔ EX c ∈ Set.range (Finsupp.mapDomain f) := by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨EA a, (happ a).symm⟩
    · rintro ⟨a, ha⟩
      refine ⟨EA.symm a, EX.injective ?_⟩
      rw [happ, EA.apply_symm_apply, ha]
  change c ∈ LinearMap.range i.hom ↔ ∀ s ∈ (EX c).support, Set.range s ⊆ A
  rw [hrange, Finsupp.mem_range_mapDomain_iff f hf]
  constructor
  · intro h s hs
    apply (hfrange s).mp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hs) (h s hn)
  · intro h s hs
    by_contra hn
    exact hs ((hfrange s).mpr (h s (Finsupp.mem_support_iff.mpr hn)))

theorem integral_chain_finite_representation (n : Nat)
    (c : (integralChains X).X n) :
    c = ∑ s ∈ (integralChainCoordinates X n c).support,
      integralSingularGenerator s (integralChainCoordinates X n c s) := by
  apply (integralChainCoordinates X n).injective
  simp only [map_sum]
  calc
    integralChainCoordinates X n c =
        ∑ s ∈ (integralChainCoordinates X n c).support,
          Finsupp.single s (integralChainCoordinates X n c s) :=
      (Finsupp.sum_single (integralChainCoordinates X n c)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact (integralChainCoordinates_generator s _).symm

theorem integral_pair_degree_split (A : Set X) (n : Nat) :
    ∃ r : (integralChains X).X n ⟶ (integralChains A).X n,
    ∃ s : (integralRelativeChains A).X n ⟶ (integralChains X).X n,
      (integralSubspaceChains A).f n ≫ r = 𝟙 _ ∧
      s ≫ (integralRelativeProjection A).f n = 𝟙 _ ∧
      r ≫ (integralSubspaceChains A).f n +
        (integralRelativeProjection A).f n ≫ s = 𝟙 _ := by
  let v : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let f : C(integralSimplex n, A) → C(integralSimplex n, X) := fun s => v.comp s
  let i := (integralSubspaceChains A).f n
  let p := (integralRelativeProjection A).f n
  let EA := integralChainCoordinates A n
  let EX := integralChainCoordinates X n
  have hf : Function.Injective f := by
    intro s t h
    ext z
    exact congrArg (fun k : C(integralSimplex n, X) => k z) h
  let r : (integralChains X).X n ⟶ (integralChains A).X n :=
    ModuleCat.ofHom (EA.symm.toLinearMap.comp
      ((Finsupp.lcomapDomain (R := Int) (M := ULift.{u} Int) f hf).comp EX.toLinearMap))
  have hgen (s : C(integralSimplex n, A)) :
      integralSingularGenerator s ≫ i = integralSingularGenerator (f s) :=
    integralSingularGenerator_map s v
  have hrgen (s : C(integralSimplex n, A)) (a : ULift.{u} Int) :
      r (integralSingularGenerator (f s) a) = integralSingularGenerator s a := by
    change EA.symm (Finsupp.comapDomain f
      (EX (integralSingularGenerator (f s) a)) hf.injOn) = integralSingularGenerator s a
    apply EA.injective
    rw [EA.apply_symm_apply, integralChainCoordinates_generator,
      integralChainCoordinates_generator, Finsupp.comapDomain_single]
  have hir : i ≫ r = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro x
    obtain ⟨s, rfl⟩ := ((TopCat.of A).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm.surjective x
    change integralSingularGenerator s ≫ (i ≫ r) = integralSingularGenerator s ≫ 𝟙 _
    rw [← Category.assoc, hgen, Category.comp_id]
    ext a
    exact hrgen s a
  let t : (integralChains X).X n ⟶ (integralChains X).X n := 𝟙 _ - r ≫ i
  have hit : i ≫ t = 0 := by
    dsimp only [t]
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hir,
      Category.id_comp, sub_self]
  let d := CokernelCofork.IsColimit.desc'
    (isColimitOfHasCokernelOfPreservesColimit
      (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)
      (integralSubspaceChains A)) t hit
  let s : (integralRelativeChains A).X n ⟶ (integralChains X).X n := d.val
  have hps : p ≫ s = t := d.property
  have hip : i ≫ p = 0 :=
    congrArg (fun q => q.f n) (cokernel.condition (integralSubspaceChains A))
  have hsp : s ≫ p = 𝟙 _ := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hps]
    dsimp only [t]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hip, comp_zero,
      sub_zero, Category.comp_id]
  refine ⟨r, s, hir, hsp, ?_⟩
  change r ≫ i + p ≫ s = 𝟙 _
  rw [hps]
  change r ≫ i + (𝟙 _ - r ≫ i) = 𝟙 _
  rw [← add_sub_assoc, add_sub_cancel_left]

end Poincare.Topology
