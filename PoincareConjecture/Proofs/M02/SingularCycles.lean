import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace PoincareConjecture.Proofs.M02

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

theorem simplicialSimplexDifference_d_eq_zero (R : C) (X : SSet.{w})
    {n : ℕ} (s t : X _⦋n + 1⦌)
    (hface : ∀ i : Fin (n + 2), X.δ i s = X.δ i t) :
    (X.ιChainComplex s - X.ιChainComplex t) ≫
      (X.chainComplex R).d (n + 1) n = 0 := by
  have hd : X.ιChainComplex s ≫ (X.chainComplex R).d (n + 1) n =
      X.ιChainComplex t ≫ (X.chainComplex R).d (n + 1) n := by
    simp only [SSet.ιChainComplex_d, hface]
  rw [Preadditive.sub_comp, hd, sub_self]

noncomputable def singularConstantSimplex (X : TopCat.{w}) (n : ℕ) (x : X) :
    (TopCat.toSSet.obj X) _⦋n⦌ :=
  (X.toSSetObjEquiv _).symm (ContinuousMap.const _ x)

theorem singularConstantSimplex_face (X : TopCat.{w}) {n : ℕ}
    (x : X) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i (singularConstantSimplex X (n + 1) x) =
      singularConstantSimplex X n x := by
  refine (X.toSSetObjEquiv _).injective ?_
  exact ContinuousMap.ext (fun _ => rfl)

theorem singularConstantSimplex_map {X Y : TopCat.{w}} (f : X ⟶ Y)
    (n : ℕ) (x : X) :
    (TopCat.toSSet.map f).app _ (singularConstantSimplex X n x) =
      singularConstantSimplex Y n (f x) := by
  refine (Y.toSSetObjEquiv _).injective ?_
  exact ContinuousMap.ext (fun _ => rfl)

theorem singularSimplexDifference_d_eq_zero (R : C) (X : TopCat.{w})
    {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (x : X)
    (hface : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x) :
    ((TopCat.toSSet.obj X).ιChainComplex s -
      (TopCat.toSSet.obj X).ιChainComplex (singularConstantSimplex X (n + 1) x)) ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n = 0 := by
  exact simplicialSimplexDifference_d_eq_zero R (TopCat.toSSet.obj X) s
    (singularConstantSimplex X (n + 1) x)
    (fun i => (hface i).trans (singularConstantSimplex_face X x i).symm)

end PoincareConjecture.Proofs.M02
