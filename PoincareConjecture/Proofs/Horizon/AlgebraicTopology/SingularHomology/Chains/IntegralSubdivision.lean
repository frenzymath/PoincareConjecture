import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Chains.IntegralTupleRealization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas








set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped BigOperators Simplicial

universe u v

namespace Poincare.Topology

def integralBarycentricSubdivision (X : Type u) [TopologicalSpace X] :
    integralChains X ⟶ integralChains X := by
  classical
  let R (n : Nat) (s : C(integralSimplex n, X)) :=
    integralTupleRealization n n s
      (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
        (Finsupp.single (integralSimplexVertices n) 1))
  let F (n : Nat) : (integralChains X).X n ⟶ (integralChains X).X n :=
    letI : MulAction Int ((integralChains X).X n) :=
      ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
    ModuleCat.ofHom
      ((Finsupp.lsum (N := (integralChains X).X n) Int
        (fun s : C(integralSimplex n, X) =>
          (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
            (M := (integralChains X).X n) (R n s))).comp
        (integralChainCoordinates X n).toLinearMap)
  have hF (n : Nat) (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
      F n (integralSingularGenerator s a) = a.down • R n s := by
    let : MulAction Int ((integralChains X).X n) :=
      ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X n) Int
      (fun t : C(integralSimplex n, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X n) (R n t)))
      (integralChainCoordinates X n (integralSingularGenerator s a)) = _
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact int_smul_eq_zsmul ((integralChains X).X n).isModule a.down _
  have hface (n : Nat) (s : C(integralSimplex (n + 1), X)) (i : Fin (n + 2)) :
      R n (s.comp (integralSimplexFace n i)) =
        integralTupleRealization (n + 1) n s
          (integralOrderedSubdivision (integralSimplexBarycenter (n + 1)) (n + 1)
            (Finsupp.single (integralSimplexVertices (n + 1) ∘ i.succAbove) 1)) := by
    let w := integralSimplexVertices (n + 1) ∘ i.succAbove
    have hw : integralSimplexAffine w = integralSimplexFace n i := by
      simpa only [w, integralSimplexAffine_vertices, ContinuousMap.id_comp] using
        (integralSimplexAffine_face (integralSimplexVertices (n + 1)) i).symm
    have hb (k : Nat) (v : Fin (k + 1) → integralSimplex n) :
        integralSimplexAffine w (integralSimplexBarycenter n k v) =
          integralSimplexBarycenter (n + 1) k (integralSimplexAffine w ∘ v) :=
      integralSimplexAffine_barycenter w v
    have hvertex : integralSimplexAffine w ∘ integralSimplexVertices n = w := by
      funext j
      exact integralSimplexAffine_vertex w j
    dsimp only [R]
    rw [← hw, integralTupleRealization_affine,
      integralOrderedSubdivision_map (integralSimplexBarycenter n)
        (integralSimplexBarycenter (n + 1)) (integralSimplexAffine w) hb,
      integralOrderedMap_single, hvertex]
  have hunit (n : Nat) (s : C(integralSimplex (n + 1), X)) :
      (integralChains X).d (n + 1) n
          (F (n + 1) (integralSingularGenerator s (ULift.up 1))) =
        F n ((integralChains X).d (n + 1) n
          (integralSingularGenerator s (ULift.up 1))) := by
    let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
        (integralChains X).X n :=
      { toFun := fun f => f (ULift.up 1)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hd := congrArg ev (integralSingularGenerator_boundary s)
    rw [map_sum] at hd
    change (integralChains X).d (n + 1) n
      (integralSingularGenerator s (ULift.up 1)) = _ at hd
    rw [hF, one_smul, hd, map_sum]
    dsimp only [R]
    rw [integralTupleRealization_boundary, integralOrderedSubdivision_boundary,
      integralOrderedBoundary_single, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_zsmul]
    have hFi : F n (ev (integralSingularGenerator (s.comp (integralSimplexFace n i)))) =
        R n (s.comp (integralSimplexFace n i)) := by
      change F n (integralSingularGenerator (s.comp (integralSimplexFace n i)) (ULift.up 1)) = _
      exact (hF n _ (ULift.up 1)).trans (one_zsmul _)
    exact congrArg (fun c : (integralChains X).X n => ((-1 : Int) ^ i.val) • c)
      ((hface n s i).symm.trans hFi.symm)
  refine { f := F, comm' := ?_ }
  intro i j hij
  change j + 1 = i at hij
  subst i
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨s, rfl⟩ :=
    ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋j + 1⦌)).symm.surjective x
  change integralSingularGenerator s ≫ (F (j + 1) ≫ (integralChains X).d (j + 1) j) =
    integralSingularGenerator s ≫ ((integralChains X).d (j + 1) j ≫ F j)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  change (integralChains X).d (j + 1) j (F (j + 1) (integralSingularGenerator s a)) =
    F j ((integralChains X).d (j + 1) j (integralSingularGenerator s a))
  rw [ha]
  simp only [map_zsmul]
  exact congrArg (fun c : (integralChains X).X j => a.down • c) (hunit j s)

def integralSubdivisionPrism (X : Type u) [TopologicalSpace X] :
    Homotopy (𝟙 (integralChains X)) (integralBarycentricSubdivision X) := by
  classical
  let R (n : Nat) (s : C(integralSimplex n, X)) :=
    integralTupleRealization n (n + 1) s
      (integralOrderedPrism (integralSimplexBarycenter n) (n + 1)
        (Finsupp.single (integralSimplexVertices n) 1))
  let T (n : Nat) : (integralChains X).X n ⟶ (integralChains X).X (n + 1) :=
    letI : MulAction Int ((integralChains X).X (n + 1)) :=
      ((integralChains X).X (n + 1)).isModule.toDistribMulAction.toMulAction
    ModuleCat.ofHom
      ((Finsupp.lsum (N := (integralChains X).X (n + 1)) Int
        (fun s : C(integralSimplex n, X) =>
          (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
            (M := (integralChains X).X (n + 1)) (R n s))).comp
        (integralChainCoordinates X n).toLinearMap)
  let P (i j : Nat) : (integralChains X).X i ⟶ (integralChains X).X j :=
    if h : i + 1 = j then T i ≫ eqToHom (congrArg (fun k => (integralChains X).X k) h)
    else 0
  have hT (n : Nat) (s : C(integralSimplex n, X)) (a : ULift.{u} Int) :
      T n (integralSingularGenerator s a) = a.down • R n s := by
    let : MulAction Int ((integralChains X).X (n + 1)) :=
      ((integralChains X).X (n + 1)).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X (n + 1)) Int
      (fun t : C(integralSimplex n, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X (n + 1)) (R n t)))
      (integralChainCoordinates X n (integralSingularGenerator s a)) = _
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact int_smul_eq_zsmul ((integralChains X).X (n + 1)).isModule a.down _
  have hS (n : Nat) (s : C(integralSimplex n, X)) :
      (integralBarycentricSubdivision X).f n (integralSingularGenerator s (ULift.up 1)) =
        integralTupleRealization n n s
          (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
            (Finsupp.single (integralSimplexVertices n) 1)) := by
    let Q (t : C(integralSimplex n, X)) :=
      integralTupleRealization n n t
        (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
          (Finsupp.single (integralSimplexVertices n) 1))
    let : MulAction Int ((integralChains X).X n) :=
      ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X n) Int
      (fun t : C(integralSimplex n, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X n) (Q t)))
      (integralChainCoordinates X n (integralSingularGenerator s (ULift.up 1))) = Q s
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact (int_smul_eq_zsmul ((integralChains X).X n).isModule 1 _).trans (one_zsmul _)
  have hface (n : Nat) (s : C(integralSimplex (n + 1), X)) (i : Fin (n + 2)) :
      R n (s.comp (integralSimplexFace n i)) =
        integralTupleRealization (n + 1) (n + 1) s
          (integralOrderedPrism (integralSimplexBarycenter (n + 1)) (n + 1)
            (Finsupp.single (integralSimplexVertices (n + 1) ∘ i.succAbove) 1)) := by
    let w := integralSimplexVertices (n + 1) ∘ i.succAbove
    have hw : integralSimplexAffine w = integralSimplexFace n i := by
      simpa only [w, integralSimplexAffine_vertices, ContinuousMap.id_comp] using
        (integralSimplexAffine_face (integralSimplexVertices (n + 1)) i).symm
    have hb (k : Nat) (v : Fin (k + 1) → integralSimplex n) :
        integralSimplexAffine w (integralSimplexBarycenter n k v) =
          integralSimplexBarycenter (n + 1) k (integralSimplexAffine w ∘ v) :=
      integralSimplexAffine_barycenter w v
    have hvertex : integralSimplexAffine w ∘ integralSimplexVertices n = w := by
      funext j
      exact integralSimplexAffine_vertex w j
    dsimp only [R]
    rw [← hw, integralTupleRealization_affine,
      integralOrderedPrism_map (integralSimplexBarycenter n)
        (integralSimplexBarycenter (n + 1)) (integralSimplexAffine w) hb,
      integralOrderedMap_single, hvertex]
  have hunit (n : Nat) (s : C(integralSimplex n, X)) :
      integralSingularGenerator s (ULift.up 1) =
        (dNext n P + prevD n P + (integralBarycentricSubdivision X).f n)
          (integralSingularGenerator s (ULift.up 1)) := by
    cases n with
    | zero =>
        have hzero : T 0 (integralSingularGenerator s (ULift.up 1)) = 0 := by
          rw [hT]
          dsimp only [R]
          rw [integralOrderedPrism_one _ (integralSimplexBarycenter_one 0),
            LinearMap.zero_apply, map_zero]
          exact one_zsmul _
        rw [dNext_eq_zero P 0 (by simp),
          prevD_eq P (show (ComplexShape.down Nat).Rel 1 0 from rfl)]
        simp only [P, dif_pos rfl, eqToHom_refl, Category.comp_id]
        change integralSingularGenerator s (ULift.up 1) =
          0 + (integralChains X).d 1 0 (T 0 (integralSingularGenerator s (ULift.up 1))) +
            (integralBarycentricSubdivision X).f 0 (integralSingularGenerator s (ULift.up 1))
        rw [hzero, map_zero, zero_add, zero_add, hS]
        rw [integralOrderedSubdivision_one _ (integralSimplexBarycenter_one 0)]
        simp only [LinearMap.id_apply, integralTupleRealization_single,
          one_smul, integralSimplexAffine_vertices, ContinuousMap.comp_id]
    | succ n =>
        let ev : (integralCoefficient.{u} ⟶ (integralChains X).X n) →+
            (integralChains X).X n :=
          { toFun := fun f => f (ULift.up 1)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        have hd := congrArg ev (integralSingularGenerator_boundary s)
        rw [map_sum] at hd
        change (integralChains X).d (n + 1) n
          (integralSingularGenerator s (ULift.up 1)) = _ at hd
        have htd : T n ((integralChains X).d (n + 1) n
            (integralSingularGenerator s (ULift.up 1))) =
          integralTupleRealization (n + 1) (n + 1) s
            (integralOrderedPrism (integralSimplexBarycenter (n + 1)) (n + 1)
              (integralOrderedBoundary (integralSimplex (n + 1)) (n + 1)
                (Finsupp.single (integralSimplexVertices (n + 1)) 1))) := by
          rw [hd, map_sum, integralOrderedBoundary_single, map_sum, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [map_zsmul]
          have hTi : T n (ev (integralSingularGenerator (s.comp (integralSimplexFace n i)))) =
              R n (s.comp (integralSimplexFace n i)) := by
            change T n
              (integralSingularGenerator (s.comp (integralSimplexFace n i)) (ULift.up 1)) = _
            exact (hT n _ (ULift.up 1)).trans (one_zsmul _)
          exact congrArg (fun c : (integralChains X).X (n + 1) =>
            ((-1 : Int) ^ i.val) • c) (hTi.trans (hface n s i))
        have hpr := congrArg (integralTupleRealization (n + 1) (n + 1) s)
          (integralOrderedPrism_boundary (integralSimplexBarycenter (n + 1))
            (n + 1) (Finsupp.single (integralSimplexVertices (n + 1)) 1))
        rw [map_add, map_sub, integralTupleRealization_single, one_smul,
          integralSimplexAffine_vertices, ContinuousMap.comp_id] at hpr
        rw [dNext_eq P (show (ComplexShape.down Nat).Rel (n + 1) n from rfl),
          prevD_eq P (show (ComplexShape.down Nat).Rel (n + 2) (n + 1) from rfl)]
        simp only [P, dif_pos rfl, eqToHom_refl, Category.comp_id]
        change integralSingularGenerator s (ULift.up 1) =
          T n ((integralChains X).d (n + 1) n (integralSingularGenerator s (ULift.up 1))) +
            (integralChains X).d (n + 2) (n + 1)
              (T (n + 1) (integralSingularGenerator s (ULift.up 1))) +
            (integralBarycentricSubdivision X).f (n + 1)
              (integralSingularGenerator s (ULift.up 1))
        rw [htd, hT, one_smul, hS]
        dsimp only [R]
        rw [integralTupleRealization_boundary]
        calc
          _ = _ := sub_eq_iff_eq_add.mp hpr.symm
          _ = _ := by abel
  refine { hom := P, zero := ?_, comm := ?_ }
  · intro i j hij
    exact dif_neg hij
  · intro n
    apply SSet.chainComplex_hom_ext
    intro x
    obtain ⟨s, rfl⟩ :=
      ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm.surjective x
    change integralSingularGenerator s ≫ 𝟙 ((integralChains X).X n) =
      integralSingularGenerator s ≫
        (dNext n P + prevD n P + (integralBarycentricSubdivision X).f n)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
      apply ULift.ext
      simp
    change integralSingularGenerator s a =
      (dNext n P + prevD n P + (integralBarycentricSubdivision X).f n)
        (integralSingularGenerator s a)
    rw [ha]
    simp only [map_zsmul]
    exact congrArg (fun c : (integralChains X).X n => a.down • c) (hunit n s)

def integralSubdivisionIterate (X : Type u) [TopologicalSpace X] (k : Nat) :
    integralChains X ⟶ integralChains X :=
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  CategoryTheory.End.asHom (S ^ k)

def integralIteratedSubdivisionPrism (X : Type u) [TopologicalSpace X]
    (k : Nat) : Homotopy (𝟙 (integralChains X)) (integralSubdivisionIterate X k) := by
  classical
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  let T := integralSubdivisionPrism X
  let P (k i j : Nat) :=
    ∑ r ∈ Finset.range k, (CategoryTheory.End.asHom (S ^ r)).f i ≫ T.hom i j
  have hstep (r i : Nat) :
      (CategoryTheory.End.asHom (S ^ r)).f i =
        dNext i (fun a b => (CategoryTheory.End.asHom (S ^ r)).f a ≫ T.hom a b) +
        prevD i (fun a b => (CategoryTheory.End.asHom (S ^ r)).f a ≫ T.hom a b) +
        (CategoryTheory.End.asHom (S ^ (r + 1))).f i := by
    have h := (T.compLeft (CategoryTheory.End.asHom (S ^ r))).comm i
    dsimp only [Homotopy.compLeft] at h
    simpa only [Category.comp_id, pow_succ',
      CategoryTheory.End.mul_def, S, CategoryTheory.End.of, CategoryTheory.End.asHom] using h
  have hc (r i : Nat) : 𝟙 ((integralChains X).X i) =
      dNext i (P r) + prevD i (P r) + (CategoryTheory.End.asHom (S ^ r)).f i := by
    induction r with
    | zero =>
        have hP : P 0 = 0 := by
          funext a b
          exact Finset.sum_range_zero _
        rw [hP, map_zero, map_zero, zero_add, zero_add]
        rfl
    | succ r ih =>
        have hP : P (r + 1) = P r +
            (fun a b => (CategoryTheory.End.asHom (S ^ r)).f a ≫ T.hom a b) := by
          funext a b
          exact Finset.sum_range_succ _ r
        rw [hP, map_add, map_add]
        calc
          _ = _ := ih
          _ = _ := by rw [hstep r i]; abel
  refine { hom := P k, zero := ?_, comm := hc k }
  intro i j hij
  dsimp only [P]
  apply Finset.sum_eq_zero
  intro r _
  rw [T.zero i j hij, CategoryTheory.Limits.comp_zero]

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {I : Type v}

theorem integralSubdivisionIterate_zero :
    integralSubdivisionIterate X 0 = 𝟙 (integralChains X) := rfl

theorem integralIteratedSubdivisionPrism_zero (i j : Nat) :
    (integralIteratedSubdivisionPrism X 0).hom i j = 0 := by
  simp only [integralIteratedSubdivisionPrism, Finset.sum_range_zero]

theorem integralSubdivision_natural (f : C(X, Y)) :
    integralBarycentricSubdivision X ≫ integralChainsFunctor.map (TopCat.ofHom f) =
      integralChainsFunctor.map (TopCat.ofHom f) ≫ integralBarycentricSubdivision Y := by
  have hS (Z : Type u) [TopologicalSpace Z] (n : Nat) (s : C(integralSimplex n, Z)) :
      (integralBarycentricSubdivision Z).f n (integralSingularGenerator s (ULift.up 1)) =
        integralTupleRealization n n s
          (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
            (Finsupp.single (integralSimplexVertices n) 1)) := by
    let Q (t : C(integralSimplex n, Z)) :=
      integralTupleRealization n n t
        (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
          (Finsupp.single (integralSimplexVertices n) 1))
    let : MulAction Int ((integralChains Z).X n) :=
      ((integralChains Z).X n).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains Z).X n) Int
      (fun t : C(integralSimplex n, Z) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains Z).X n) (Q t)))
      (integralChainCoordinates Z n (integralSingularGenerator s (ULift.up 1))) = Q s
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact (int_smul_eq_zsmul ((integralChains Z).X n).isModule 1 _).trans (one_zsmul _)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨s, rfl⟩ :=
    ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm.surjective x
  change integralSingularGenerator s ≫
      ((integralBarycentricSubdivision X).f n ≫
        (integralChainsFunctor.map (TopCat.ofHom f)).f n) =
    integralSingularGenerator s ≫
      ((integralChainsFunctor.map (TopCat.ofHom f)).f n ≫
        (integralBarycentricSubdivision Y).f n)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  have hg : (integralChainsFunctor.map (TopCat.ofHom f)).f n
      (integralSingularGenerator s (ULift.up 1)) =
        integralSingularGenerator (f.comp s) (ULift.up 1) :=
    congrArg (fun q : integralCoefficient.{u} ⟶ (integralChains Y).X n => q (ULift.up 1))
      (integralSingularGenerator_map s f)
  change (integralChainsFunctor.map (TopCat.ofHom f)).f n
      ((integralBarycentricSubdivision X).f n (integralSingularGenerator s a)) =
    (integralBarycentricSubdivision Y).f n
      ((integralChainsFunctor.map (TopCat.ofHom f)).f n (integralSingularGenerator s a))
  rw [ha]
  simp only [map_zsmul]
  apply congrArg (fun c : (integralChains Y).X n => a.down • c)
  rw [hS, integralTupleRealization_natural, hg, hS]

theorem integralSubdivision_small (U : I → Set X) (n : Nat)
    (c : (integralChains X).X n) (hc : c ∈ integralSmallChains U n) :
    (integralBarycentricSubdivision X).f n c ∈ integralSmallChains U n := by
  have hle : integralSmallChains U n ≤
      (integralSmallChains U n).comap ((integralBarycentricSubdivision X).f n).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change (integralBarycentricSubdivision X).f n
      (integralSingularGenerator s.val (ULift.up 1)) ∈ integralSmallChains U n
    have hS : (integralBarycentricSubdivision X).f n
        (integralSingularGenerator s.val (ULift.up 1)) =
      integralTupleRealization n n s.val
        (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
          (Finsupp.single (integralSimplexVertices n) 1)) := by
      let Q (t : C(integralSimplex n, X)) :=
        integralTupleRealization n n t
          (integralOrderedSubdivision (integralSimplexBarycenter n) (n + 1)
            (Finsupp.single (integralSimplexVertices n) 1))
      let : MulAction Int ((integralChains X).X n) :=
        ((integralChains X).X n).isModule.toDistribMulAction.toMulAction
      change (Finsupp.lsum (N := (integralChains X).X n) Int
        (fun t : C(integralSimplex n, X) =>
          (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
            (M := (integralChains X).X n) (Q t)))
        (integralChainCoordinates X n (integralSingularGenerator s.val (ULift.up 1))) = Q s.val
      rw [integralChainCoordinates_generator, Finsupp.lsum_single,
        LinearMap.smulRight_apply]
      exact (int_smul_eq_zsmul ((integralChains X).X n).isModule 1 _).trans (one_zsmul _)
    rw [hS]
    exact integralTupleRealization_small U n n s.val s.property _
  exact hle hc

theorem integralIteratedSubdivisionPrism_small (U : I → Set X) (k i j : Nat)
    (c : (integralChains X).X i) (hc : c ∈ integralSmallChains U i) :
    (integralIteratedSubdivisionPrism X k).hom i j c ∈ integralSmallChains U j := by
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  have hpow (r n : Nat) (c : (integralChains X).X n)
      (hc : c ∈ integralSmallChains U n) :
      (CategoryTheory.End.asHom (S ^ r)).f n c ∈ integralSmallChains U n := by
    induction r with
    | zero => simpa using hc
    | succ r ih =>
        rw [pow_succ', CategoryTheory.End.mul_def]
        exact integralSubdivision_small U n _ ih
  have hT (a b : Nat) (c : (integralChains X).X a)
      (hc : c ∈ integralSmallChains U a) :
      (integralSubdivisionPrism X).hom a b c ∈ integralSmallChains U b := by
    by_cases hab : a + 1 = b
    · subst b
      have hle : integralSmallChains U a ≤ (integralSmallChains U (a + 1)).comap
          ((integralSubdivisionPrism X).hom a (a + 1)).hom := by
        apply Submodule.span_le.mpr
        rintro _ ⟨s, rfl⟩
        change (integralSubdivisionPrism X).hom a (a + 1)
          (integralSingularGenerator s.val (ULift.up 1)) ∈ integralSmallChains U (a + 1)
        have hgen : (integralSubdivisionPrism X).hom a (a + 1)
            (integralSingularGenerator s.val (ULift.up 1)) =
          integralTupleRealization a (a + 1) s.val
            (integralOrderedPrism (integralSimplexBarycenter a) (a + 1)
              (Finsupp.single (integralSimplexVertices a) 1)) := by
          let Q (t : C(integralSimplex a, X)) :=
            integralTupleRealization a (a + 1) t
              (integralOrderedPrism (integralSimplexBarycenter a) (a + 1)
                (Finsupp.single (integralSimplexVertices a) 1))
          let : MulAction Int ((integralChains X).X (a + 1)) :=
            ((integralChains X).X (a + 1)).isModule.toDistribMulAction.toMulAction
          simp only [integralSubdivisionPrism, dif_pos rfl, eqToHom_refl]
          change (Finsupp.lsum (N := (integralChains X).X (a + 1)) Int
            (fun t : C(integralSimplex a, X) =>
              (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
                (M := (integralChains X).X (a + 1)) (Q t)))
            (integralChainCoordinates X a (integralSingularGenerator s.val (ULift.up 1))) = Q s.val
          rw [integralChainCoordinates_generator, Finsupp.lsum_single,
            LinearMap.smulRight_apply]
          exact (int_smul_eq_zsmul ((integralChains X).X (a + 1)).isModule 1 _).trans (one_zsmul _)
        rw [hgen]
        exact integralTupleRealization_small U a (a + 1) s.val s.property _
      exact hle hc
    · rw [(integralSubdivisionPrism X).zero a b hab]
      exact (integralSmallChains U b).zero_mem
  change ((∑ r ∈ Finset.range k,
    (CategoryTheory.End.asHom (S ^ r)).f i ≫ (integralSubdivisionPrism X).hom i j).hom) c ∈ _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro r _
  exact hT i j _ (hpow r i c hc)

theorem integral_subdivision_eventually_small (U : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ)
    (n : Nat) (c : (integralChains X).X n) :
    ∃ k : Nat, (integralSubdivisionIterate X k).f n c ∈ integralSmallChains U n := by
  let S : CategoryTheory.End (integralChains X) :=
    CategoryTheory.End.of (integralBarycentricSubdivision X)
  have hS (m : Nat) (s : C(integralSimplex m, X)) :
      (integralBarycentricSubdivision X).f m (integralSingularGenerator s (ULift.up 1)) =
        integralTupleRealization m m s
          (integralOrderedSubdivision (integralSimplexBarycenter m) (m + 1)
            (Finsupp.single (integralSimplexVertices m) 1)) := by
    let Q (t : C(integralSimplex m, X)) :=
      integralTupleRealization m m t
        (integralOrderedSubdivision (integralSimplexBarycenter m) (m + 1)
          (Finsupp.single (integralSimplexVertices m) 1))
    let : MulAction Int ((integralChains X).X m) :=
      ((integralChains X).X m).isModule.toDistribMulAction.toMulAction
    change (Finsupp.lsum (N := (integralChains X).X m) Int
      (fun t : C(integralSimplex m, X) =>
        (ULift.moduleEquiv : ULift.{u} Int ≃ₗ[Int] Int).toLinearMap.smulRight
          (M := (integralChains X).X m) (Q t)))
      (integralChainCoordinates X m (integralSingularGenerator s (ULift.up 1))) = Q s
    rw [integralChainCoordinates_generator, Finsupp.lsum_single,
      LinearMap.smulRight_apply]
    exact (int_smul_eq_zsmul ((integralChains X).X m).isModule 1 _).trans (one_zsmul _)

  have hreal (d m : Nat) (s : C(integralSimplex d, X))
      (b : integralOrderedChains (integralSimplex d) (m + 1)) :
      (integralBarycentricSubdivision X).f m (integralTupleRealization d m s b) =
        integralTupleRealization d m s
          (integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1) b) := by
    have he : ((integralBarycentricSubdivision X).f m).hom.comp
          (integralTupleRealization d m s) =
        (integralTupleRealization d m s).comp
          (integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1)) := by
      apply Finsupp.lhom_ext'
      intro w
      apply LinearMap.ext_ring
      change (integralBarycentricSubdivision X).f m
          (integralTupleRealization d m s (Finsupp.single w 1)) =
        integralTupleRealization d m s
          (integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1)
            (Finsupp.single w 1))
      have hb (k : Nat) (v : Fin (k + 1) → integralSimplex m) :
          integralSimplexAffine w (integralSimplexBarycenter m k v) =
            integralSimplexBarycenter d k (integralSimplexAffine w ∘ v) :=
        integralSimplexAffine_barycenter w v
      have hvertex : integralSimplexAffine w ∘ integralSimplexVertices m = w := by
        funext i
        exact integralSimplexAffine_vertex w i
      rw [integralTupleRealization_single, one_smul, hS,
        integralTupleRealization_affine,
        integralOrderedSubdivision_map (integralSimplexBarycenter m)
          (integralSimplexBarycenter d) (integralSimplexAffine w) hb,
        integralOrderedMap_single, hvertex]
    exact LinearMap.congr_fun he b
  have hiter (r d m : Nat) (s : C(integralSimplex d, X))
      (b : integralOrderedChains (integralSimplex d) (m + 1)) :
      (CategoryTheory.End.asHom (S ^ r)).f m (integralTupleRealization d m s b) =
        integralTupleRealization d m s
          ((integralOrderedSubdivision (integralSimplexBarycenter d) (m + 1) ^ r) b) := by
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [pow_succ', CategoryTheory.End.mul_def]
        change (integralBarycentricSubdivision X).f m
            ((CategoryTheory.End.asHom (S ^ r)).f m (integralTupleRealization d m s b)) = _
        rw [ih, hreal, pow_succ', Module.End.mul_apply]
  have hpow (r m : Nat) (b : (integralChains X).X m)
      (hb : b ∈ integralSmallChains U m) :
      (CategoryTheory.End.asHom (S ^ r)).f m b ∈ integralSmallChains U m := by
    induction r with
    | zero => simpa using hb
    | succ r ih =>
        rw [pow_succ', CategoryTheory.End.mul_def]
        exact integralSubdivision_small U m _ ih
  have hgen (s : C(integralSimplex n, X)) :
      ∃ r : Nat, (CategoryTheory.End.asHom (S ^ r)).f n
        (integralSingularGenerator s (ULift.up 1)) ∈ integralSmallChains U n := by
    cases n with
    | zero =>
        have hx : s (integralSimplexVertices 0 0) ∈ ⋃ i, U i := by
          rw [hcover]
          exact Set.mem_univ _
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        have hs : IntegralSmallSimplex U s := by
          refine ⟨i, ?_⟩
          rintro _ ⟨z, rfl⟩
          simpa only [Subsingleton.elim z (integralSimplexVertices 0 0)] using hi
        refine ⟨0, ?_⟩
        change integralSingularGenerator s (ULift.up 1) ∈ integralSmallChains U 0
        exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
    | succ m =>
        let V : I → Set (integralSimplex (m + 1)) := fun i => s ⁻¹' U i
        have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage s.continuous
        have hVc : Set.univ ⊆ ⋃ i, V i := by
          intro z _
          have hz : s z ∈ ⋃ i, U i := by rw [hcover]; exact Set.mem_univ _
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        obtain ⟨δ, hδ, hball⟩ :=
          lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ hV hVc
        let q : Real := ((m + 1 : Nat) : Real) / (((m + 1 : Nat) : Real) + 1)
        have hq0 : 0 ≤ q := by dsimp only [q]; positivity
        have hq1 : q < 1 := by
          dsimp only [q]
          rw [div_lt_one (by positivity)]
          exact lt_add_one _
        have hlim : ∀ᶠ r in Filter.atTop, q ^ r < δ :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually (gt_mem_nhds hδ)
        obtain ⟨r, hr⟩ := hlim.exists
        let b := (integralOrderedSubdivision (integralSimplexBarycenter (m + 1))
          (m + 2) ^ r) (Finsupp.single (integralSimplexVertices (m + 1)) 1)
        have hvertices (i j : Fin (m + 2)) :
            dist (integralSimplexVertices (m + 1) i)
              (integralSimplexVertices (m + 1) j) ≤ 1 := by
          exact (Metric.dist_le_diam_of_mem
            (isCompact_stdSimplex Real (Fin (m + 2))).isBounded
            (integralSimplexVertices (m + 1) i).property
            (integralSimplexVertices (m + 1) j).property).trans diam_stdSimplex_le
        have hsmall (w : Fin (m + 2) → integralSimplex (m + 1)) (hw : w ∈ b.support) :
            IntegralSmallSimplex U (s.comp (integralSimplexAffine w)) := by
          have hmesh : ∀ i j, dist (w i) (w j) ≤ q ^ r := by
            simpa only [q, mul_one] using
              integralSimplexSubdivision_iterate_mesh r (integralSimplexVertices (m + 1))
                1 zero_le_one hvertices w hw
          obtain ⟨i, hi⟩ := hball (w 0) (Set.mem_univ _)
          refine ⟨i, ?_⟩
          rintro _ ⟨z, rfl⟩
          apply hi
          change dist (integralSimplexAffine w z) (w 0) < δ
          have hd := integralSimplexAffine_dist_le w (q ^ r) (pow_nonneg hq0 r)
            hmesh z (integralSimplexVertices (m + 1) 0)
          rw [integralSimplexAffine_vertex] at hd
          exact hd.trans_lt hr
        have hbase : integralTupleRealization (m + 1) (m + 1) s
            (Finsupp.single (integralSimplexVertices (m + 1)) 1) =
              integralSingularGenerator s (ULift.up 1) := by
          rw [integralTupleRealization_single, one_smul,
            integralSimplexAffine_vertices, ContinuousMap.comp_id]
        refine ⟨r, ?_⟩
        rw [← hbase, hiter]
        change integralTupleRealization (m + 1) (m + 1) s b ∈ integralSmallChains U (m + 1)
        rw [← Finsupp.sum_single b]
        change integralTupleRealization (m + 1) (m + 1) s
          (∑ w ∈ b.support, Finsupp.single w (b w)) ∈ integralSmallChains U (m + 1)
        rw [map_sum]
        apply Submodule.sum_mem
        intro w hw
        rw [integralTupleRealization_single]
        apply (integralSmallChains U (m + 1)).toAddSubgroup.zsmul_mem
        exact Submodule.subset_span ⟨⟨_, hsmall w hw⟩, rfl⟩
  choose count hcount using hgen
  let k := (integralChainCoordinates X n c).support.sup count
  refine ⟨k, ?_⟩
  change (CategoryTheory.End.asHom (S ^ k)).f n c ∈ integralSmallChains U n
  rw [integral_chain_finite_representation n c, map_sum]
  apply Submodule.sum_mem
  intro s hs
  let a := integralChainCoordinates X n c s
  have ha : a = a.down • (ULift.up 1 : ULift.{u} Int) := by
    apply ULift.ext
    simp
  change (CategoryTheory.End.asHom (S ^ k)).f n (integralSingularGenerator s a) ∈ _
  rw [ha]
  simp only [map_zsmul]
  apply (integralSmallChains U n).toAddSubgroup.zsmul_mem
  have hle : count s ≤ k := Finset.le_sup hs
  have hk : k = (k - count s) + count s := (Nat.sub_add_cancel hle).symm
  rw [hk, pow_add, CategoryTheory.End.mul_def]
  exact hpow (k - count s) n _ (hcount s)

end Poincare.Topology
