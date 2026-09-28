import PoincareConjecture.Proofs.M02.Topology.SingularSimplexLoops
import PoincareConjecture.Proofs.M02.Topology.SingularSimplexDescent

set_option autoImplicit false

open CategoryTheory Simplicial

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable def stdSimplexCubeMap (n : Nat) :
    C((Fin n -> unitInterval), stdSimplex Real (Fin (n + 1))) :=
  (exists_stdSimplex_cube_coordinates n).choose

theorem stdSimplexCubeMap_spec (n : Nat) :
    And (forall t, stdSimplexCubeMap n t 0 = ∏ k : Fin n, (1 - (t k : Real)))
      (forall t (j : Fin n), stdSimplexCubeMap n t j.succ =
        (t j : Real) * ∏ k : Fin n, if j < k then 1 - (t k : Real) else 1) :=
  (exists_stdSimplex_cube_coordinates n).choose_spec

noncomputable def singularPointedSimplexGenLoop (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a : (TopCat.toSSet.obj X).PtSimplex (n + 1) x) :
    GenLoop (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x) :=
  (exists_singular_pointedSimplex_genLoop X n x a (stdSimplexCubeMap (n + 1))
    (fun t ht => (stdSimplex_cube_coordinates_boundary_iff (n + 1) _
      (stdSimplexCubeMap_spec (n + 1)).1 (stdSimplexCubeMap_spec (n + 1)).2 t).mpr ht)).choose

theorem singularPointedSimplexGenLoop_val (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a : (TopCat.toSSet.obj X).PtSimplex (n + 1) x) :
    (singularPointedSimplexGenLoop X n x a).val =
      (X.toSSetObjEquiv _ (SSet.yonedaEquiv a.map)).comp (stdSimplexCubeMap (n + 1)) :=
  (exists_singular_pointedSimplex_genLoop X n x a (stdSimplexCubeMap (n + 1))
    (fun t ht => (stdSimplex_cube_coordinates_boundary_iff (n + 1) _
      (stdSimplexCubeMap_spec (n + 1)).1 (stdSimplexCubeMap_spec (n + 1)).2 t).mpr ht)).choose_spec

noncomputable def singularPointedSimplexClass (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a : (TopCat.toSSet.obj X).PtSimplex (n + 1) x) :
    HomotopyGroup (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x) :=
  Quotient.mk _ (singularPointedSimplexGenLoop X n x a)

theorem singularPointedSimplexClass_const (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))) :
    singularPointedSimplexClass X n x SSet.RelativeMorphism.const = 1 := by
  have h : singularPointedSimplexGenLoop X n x SSet.RelativeMorphism.const =
      (GenLoop.const : GenLoop (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x)) := by
    apply Subtype.ext
    rw [singularPointedSimplexGenLoop_val]
    ext t
    exact singular_const_apply X (n + 1) x _
  exact (congrArg (fun f : GenLoop (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x) =>
    (Quotient.mk _ f : HomotopyGroup (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x))) h).trans
      (HomotopyGroup.one_def (N := Fin (n + 1)) (X := X) (x := TopCat.toSSetObj₀Equiv x)).symm

theorem singularPointedSimplexClass_eq_of_relStruct (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a b : (TopCat.toSSet.obj X).PtSimplex (n + 1) x) (i : Fin (n + 2))
    (r : SSet.PtSimplex.RelStruct a b i) :
    singularPointedSimplexClass X n x a = singularPointedSimplexClass X n x b := by
  have H := singular_relStruct_genLoop_homotopic X (n + 1) x a b i r
    (stdSimplexCubeMap (n + 1))
    (fun t ht => (stdSimplex_cube_coordinates_boundary_iff (n + 1) _
      (stdSimplexCubeMap_spec (n + 1)).1 (stdSimplexCubeMap_spec (n + 1)).2 t).mpr ht)
    (singularPointedSimplexGenLoop X n x a) (singularPointedSimplexGenLoop X n x b)
    (singularPointedSimplexGenLoop_val X n x a) (singularPointedSimplexGenLoop_val X n x b)
  exact Quotient.sound H

theorem singularPointedSimplexClass_mul (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (a b c : (TopCat.toSSet.obj X).PtSimplex (n + 2) x)
    (r : SSet.PtSimplex.MulStruct a b c (0 : Fin (n + 2))) :
    singularPointedSimplexClass X (n + 1) x c =
      singularPointedSimplexClass X (n + 1) x a * singularPointedSimplexClass X (n + 1) x b := by
  exact singular_mulStruct_genLoop_mul X n x a b c r (stdSimplexCubeMap (n + 2))
    (stdSimplexCubeMap_spec (n + 2)).1 (stdSimplexCubeMap_spec (n + 2)).2
    (singularPointedSimplexGenLoop X (n + 1) x a)
    (singularPointedSimplexGenLoop X (n + 1) x b)
    (singularPointedSimplexGenLoop X (n + 1) x c)
    (singularPointedSimplexGenLoop_val X (n + 1) x a)
    (singularPointedSimplexGenLoop_val X (n + 1) x b)
    (singularPointedSimplexGenLoop_val X (n + 1) x c)

theorem singularPointedSimplexClass_surjective (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0))) :
    Function.Surjective (singularPointedSimplexClass X n x) := by
  intro y
  refine Quotient.inductionOn y ?_
  intro f
  obtain ⟨a, ha⟩ := exists_singular_pointedSimplex_of_genLoop X n x (stdSimplexCubeMap (n + 1))
    (stdSimplexCubeMap_spec (n + 1)).1 (stdSimplexCubeMap_spec (n + 1)).2 f
  refine ⟨a, ?_⟩
  have h : singularPointedSimplexGenLoop X n x a = f :=
    Subtype.ext ((singularPointedSimplexGenLoop_val X n x a).trans ha)
  exact congrArg (fun g : GenLoop (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x) =>
    (Quotient.mk _ g : HomotopyGroup (Fin (n + 1)) X (TopCat.toSSetObj₀Equiv x))) h

end PoincareConjecture.Proofs.M02.Topology
