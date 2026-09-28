import PoincareConjecture.Proofs.M02.SimplexPrism
import PoincareConjecture.Proofs.M02.IntegralChains








set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace PoincareConjecture.Proofs.M02


theorem singularSimplexFamily_cycle_homology_factorization
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    [CategoryWithHomology C] (R : C) (X : TopCat.{w}) (x : X) {n : ℕ}
    (r : (TopCat.toSSet.obj X) _⦋n + 1⦌ → (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (H : ∀ s, ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ (r s)))
    (K : ∀ s : (TopCat.toSSet.obj X) _⦋n⦌,
      ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (ContinuousMap.const _ x))
    (hface : ∀ s (i : Fin (n + 2)),
      (TopCat.toSSet.obj X).δ i (r s) = singularConstantSimplex X n x)
    (htrace : ∀ s (i : Fin (n + 2)) (t : unitInterval) (a : stdSimplex ℝ (Fin (n + 1))),
      H s (t, stdSimplex.map i.succAbove a) = K ((TopCat.toSSet.obj X).δ i s) (t, a))
    {A : C} (z : A ⟶ ((TopCat.toSSet.obj X).chainComplex R).X (n + 1))
    (hz : z ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n = 0) :
    ((TopCat.toSSet.obj X).chainComplex R).liftCycles z n (by simp) hz ≫
        ((TopCat.toSSet.obj X).chainComplex R).homologyπ (n + 1) =
      z ≫ Sigma.desc (fun s => singularSimplexHomologyClass R X (r s) x (hface s)) := by
  let Y := TopCat.toSSet.obj X
  let Cx := Y.chainComplex R
  let f : Y ⟶ Y := TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.const X x))
  let U : Cx ⟶ Cx := SSet.chainComplexMap f R
  let T := singularSimplexFamilyMap R X r
  let L := Cx.liftCycles z n (by simp) hz
  let d (s : Y _⦋n + 1⦌) : R ⟶ Cx.cycles (n + 1) :=
    Cx.liftCycles (Y.ιChainComplex (r s) -
      Y.ιChainComplex (singularConstantSimplex X (n + 1) x)) n (by simp)
      (singularSimplexDifference_d_eq_zero R X (r s) x (hface s))
  let D : Cx.X (n + 1) ⟶ Cx.cycles (n + 1) := Sigma.desc d
  have hDbasis (s : Y _⦋n + 1⦌) : Y.ιChainComplex s ≫ D = d s :=
    Sigma.ι_desc d s
  have hTbasis (s : Y _⦋n + 1⦌) : Y.ιChainComplex s ≫ T = Y.ιChainComplex (r s) :=
    Sigma.ι_desc (fun a => Y.ιChainComplex (r a)) s
  have hconst (s : Y _⦋n + 1⦌) : f.app _ s = singularConstantSimplex X (n + 1) x := by
    apply (X.toSSetObjEquiv _).injective
    ext a
    rfl
  have hD : D ≫ Cx.iCycles (n + 1) = T - U.f (n + 1) := by
    apply SSet.chainComplex_hom_ext
    intro s
    rw [← Category.assoc, hDbasis, Preadditive.comp_sub, hTbasis]
    simp only [d, HomologicalComplex.liftCycles_i, U,
      SSet.ι_chainComplexMap_f, hconst]
  have hDπ : D ≫ Cx.homologyπ (n + 1) =
      Sigma.desc (fun s => singularSimplexHomologyClass R X (r s) x (hface s)) := by
    apply SSet.chainComplex_hom_ext
    intro s
    rw [← Category.assoc, hDbasis]
    exact (Sigma.ι_desc
      (fun a => singularSimplexHomologyClass R X (r a) x (hface a)) s).symm
  let K' (s : Y _⦋n⦌) := (K s).cast rfl
    (show ContinuousMap.const _ x = X.toSSetObjEquiv _ (singularConstantSimplex X n x) by
      simp only [singularConstantSimplex, Equiv.apply_symm_apply])
  let B := z ≫ singularSimplexFamilyPrism R X r H
  have hB : z - z ≫ T = B ≫ Cx.d (n + 2) (n + 1) :=
    singularSimplexFamily_cycle_difference_boundary R X r
      (fun _ => singularConstantSimplex X n x) H K' htrace z hz
  have hL : L - z ≫ D = B ≫ Cx.toCycles (n + 2) (n + 1) +
      L ≫ HomologicalComplex.cyclesMap U (n + 1) := by
    apply (cancel_mono (Cx.iCycles (n + 1))).mp
    simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.assoc, hD,
      Preadditive.comp_sub, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.toCycles_i, L, HomologicalComplex.liftCycles_i,
      HomologicalComplex.liftCycles_i_assoc]
    rw [← hB]
    abel
  have hzero : HomologicalComplex.homologyMap U (n + 1) = 0 :=
    singularHomologyMap_const_eq_zero R X X n x
  have hclass : L ≫ Cx.homologyπ (n + 1) -
      (z ≫ D) ≫ Cx.homologyπ (n + 1) = 0 := by
    rw [← Preadditive.sub_comp, hL, Preadditive.add_comp, Category.assoc,
      HomologicalComplex.toCycles_comp_homologyπ, comp_zero, zero_add,
      Category.assoc, ← HomologicalComplex.homologyπ_naturality]
    simp only [hzero, comp_zero]
  change L ≫ Cx.homologyπ (n + 1) = _
  rw [← hDπ, ← Category.assoc]
  exact sub_eq_zero.mp hclass

end PoincareConjecture.Proofs.M02
