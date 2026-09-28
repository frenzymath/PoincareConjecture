import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralSmallChains
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralSimplexSubdivisionGeometry







set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u v

namespace Poincare.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {I : Type v}

def integralTupleRealization (d n : Nat) (s : C(integralSimplex d, X)) :
    integralOrderedChains (integralSimplex d) (n + 1) →ₗ[Int]
      (integralChains X).X n :=
  letI : MulAction Int ((integralChains X).X n) :=
    ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
  Finsupp.lsum (N := (integralChains X).X n) Int
    (fun v : Fin (n + 1) → integralSimplex d =>
      (LinearMap.id : Int →ₗ[Int] Int).smulRight (M := (integralChains X).X n)
        (integralSingularGenerator (s.comp (integralSimplexAffine v)) (ULift.up 1)))

theorem integralTupleRealization_single (d n : Nat)
    (s : C(integralSimplex d, X))
    (v : Fin (n + 1) → integralSimplex d) (a : Int) :
    integralTupleRealization d n s (Finsupp.single v a) =
      a • integralSingularGenerator (s.comp (integralSimplexAffine v)) (ULift.up 1) := by
  simp only [integralTupleRealization, Finsupp.lsum_single,
    LinearMap.smulRight_apply, LinearMap.id_apply]
  exact int_smul_eq_zsmul ((integralChains X).X n).isModule a _

theorem integralTupleRealization_boundary (d n : Nat)
    (s : C(integralSimplex d, X))
    (c : integralOrderedChains (integralSimplex d) (n + 2)) :
    (integralChains X).d (n + 1) n (integralTupleRealization d (n + 1) s c) =
      integralTupleRealization d n s
        (integralOrderedBoundary (integralSimplex d) (n + 1) c) := by
  have h : ((integralChains X).d (n + 1) n).hom.comp
        (integralTupleRealization d (n + 1) s) =
      (integralTupleRealization d n s).comp
        (integralOrderedBoundary (integralSimplex d) (n + 1)) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change (integralChains X).d (n + 1) n
        (integralTupleRealization d (n + 1) s (Finsupp.single v 1)) =
      integralTupleRealization d n s
        (integralOrderedBoundary (integralSimplex d) (n + 1) (Finsupp.single v 1))
    rw [integralTupleRealization_single, one_smul,
      integralOrderedBoundary_single, map_sum]
    simp only [map_zsmul, integralTupleRealization_single, one_smul]
    let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
        (integralChains X).X n :=
      { toFun := fun f => f (ULift.up 1)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hg := congrArg ev
      (integralSingularGenerator_boundary (s.comp (integralSimplexAffine v)))
    rw [map_sum] at hg
    change (integralChains X).d (n + 1) n
      (integralSingularGenerator (s.comp (integralSimplexAffine v)) (ULift.up 1)) = _ at hg
    rw [hg]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    apply congrArg (fun x : (integralChains X).X n => ((-1 : Int) ^ i.val) • x)
    change integralSingularGenerator
        (s.comp ((integralSimplexAffine v).comp (integralSimplexFace n i)))
          (ULift.up 1) =
      integralSingularGenerator (s.comp (integralSimplexAffine (v ∘ i.succAbove)))
        (ULift.up 1)
    rw [integralSimplexAffine_face]
  exact LinearMap.congr_fun h c

theorem integralTupleRealization_affine {d e : Nat} (n : Nat)
    (v : Fin (d + 1) → integralSimplex e) (s : C(integralSimplex e, X))
    (c : integralOrderedChains (integralSimplex d) (n + 1)) :
    integralTupleRealization d n (s.comp (integralSimplexAffine v)) c =
      integralTupleRealization e n s
        (integralOrderedMap (n + 1) (integralSimplexAffine v) c) := by
  have h : integralTupleRealization d n (s.comp (integralSimplexAffine v)) =
      (integralTupleRealization e n s).comp
        (integralOrderedMap (n + 1) (integralSimplexAffine v)) := by
    apply Finsupp.lhom_ext
    intro w a
    change integralTupleRealization d n (s.comp (integralSimplexAffine v))
        (Finsupp.single w a) =
      integralTupleRealization e n s
        (integralOrderedMap (n + 1) (integralSimplexAffine v) (Finsupp.single w a))
    rw [integralOrderedMap_single, integralTupleRealization_single,
      integralTupleRealization_single]
    apply congrArg (fun x : (integralChains X).X n => a • x)
    change integralSingularGenerator
        (s.comp ((integralSimplexAffine v).comp (integralSimplexAffine w)))
          (ULift.up 1) =
      integralSingularGenerator
        (s.comp (integralSimplexAffine ((integralSimplexAffine v) ∘ w))) (ULift.up 1)
    rw [integralSimplexAffine_comp]
    rfl
  exact LinearMap.congr_fun h c

theorem integralTupleRealization_natural (d n : Nat)
    (s : C(integralSimplex d, X)) (f : C(X, Y))
    (c : integralOrderedChains (integralSimplex d) (n + 1)) :
    (integralChainsFunctor.map (TopCat.ofHom f)).f n
      (integralTupleRealization d n s c) =
        integralTupleRealization d n (f.comp s) c := by
  have h : ((integralChainsFunctor.map (TopCat.ofHom f)).f n).hom.comp
        (integralTupleRealization d n s) =
      integralTupleRealization d n (f.comp s) := by
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change (integralChainsFunctor.map (TopCat.ofHom f)).f n
        (integralTupleRealization d n s (Finsupp.single v 1)) =
      integralTupleRealization d n (f.comp s) (Finsupp.single v 1)
    simp only [integralTupleRealization_single, one_smul]
    exact congrArg
      (fun g : integralCoefficient.{u} ⟶ (integralChains Y).X n => g (ULift.up 1))
      (integralSingularGenerator_map (s.comp (integralSimplexAffine v)) f)
  exact LinearMap.congr_fun h c

theorem integralTupleRealization_small (U : I → Set X) (d n : Nat)
    (s : C(integralSimplex d, X)) (hs : IntegralSmallSimplex U s)
    (c : integralOrderedChains (integralSimplex d) (n + 1)) :
    integralTupleRealization d n s c ∈ integralSmallChains U n := by
  classical
  have hgen (v : Fin (n + 1) → integralSimplex d) (a : Int) :
      integralTupleRealization d n s (Finsupp.single v a) ∈
        integralSmallChains U n := by
    rw [integralTupleRealization_single]
    apply (integralSmallChains U n).toAddSubgroup.zsmul_mem
    apply Submodule.subset_span
    refine ⟨⟨s.comp (integralSimplexAffine v), ?_⟩, rfl⟩
    rcases hs with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨integralSimplexAffine v z, rfl⟩
  rw [← Finsupp.sum_single c]
  change integralTupleRealization d n s
    (∑ v ∈ c.support, Finsupp.single v (c v)) ∈ integralSmallChains U n
  rw [map_sum]
  apply Submodule.sum_mem
  intro v _
  exact hgen v (c v)

end Poincare.Topology
