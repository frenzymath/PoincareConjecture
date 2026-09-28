import PoincareConjecture.Proofs.M02.SingularCycles

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe w v u

namespace PoincareConjecture.Proofs.M02

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

theorem simplicialPrism_onSimplex (R : C) {X Y : SSet.{w}}
    {f g : X ⟶ Y} (H : SimplicialObject.Homotopy f g)
    {n : ℕ} (s : X _⦋n⦌) :
    X.ιChainComplex s ≫ (H.sSetChainComplexMap R).hom n (n + 1) =
      -∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • Y.ιChainComplex (H.h i s) := by
  change X.ιChainComplex s ≫ SimplicialObject.Homotopy.ToChainHomotopy.hom
    (H.whiskerRight (sigmaConst.obj R)) n (n + 1) = _
  rw [SimplicialObject.Homotopy.ToChainHomotopy.hom_eq]
  simp only [Preadditive.comp_neg, Preadditive.comp_sum, Preadditive.comp_zsmul]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  change Sigma.ι (fun _ : X _⦋n⦌ => R) s ≫ (sigmaConst.obj R).map (H.h i) = _
  simp [sigmaConst, Sigma.map', SSet.ιChainComplex]

theorem simplicialPrism_difference_boundary (R : C) {X Y : SSet.{w}}
    {f g p q : X ⟶ Y} (H : SimplicialObject.Homotopy f g)
    (K : SimplicialObject.Homotopy p q) {n : ℕ} (s : X _⦋n + 1⦌)
    (hface : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)),
      H.h j (X.δ i s) = K.h j (X.δ i s)) :
    (X.ιChainComplex s ≫ (H.sSetChainComplexMap R).hom (n + 1) (n + 2) -
      X.ιChainComplex s ≫ (K.sSetChainComplexMap R).hom (n + 1) (n + 2)) ≫
        (Y.chainComplex R).d (n + 2) (n + 1) =
      (Y.ιChainComplex (f.app _ s) - Y.ιChainComplex (g.app _ s)) -
        (Y.ιChainComplex (p.app _ s) - Y.ιChainComplex (q.app _ s)) := by
  have hside :
      X.ιChainComplex s ≫ (X.chainComplex R).d (n + 1) n ≫
          (H.sSetChainComplexMap R).hom n (n + 1) =
        X.ιChainComplex s ≫ (X.chainComplex R).d (n + 1) n ≫
          (K.sSetChainComplexMap R).hom n (n + 1) := by
    simp only [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp,
      Preadditive.zsmul_comp, simplicialPrism_onSimplex, hface]
  have hH := congrArg (fun a => X.ιChainComplex s ≫ a)
    ((H.sSetChainComplexMap R).comm (n + 1))
  have hK := congrArg (fun a => X.ιChainComplex s ≫ a)
    ((K.sSetChainComplexMap R).comm (n + 1))
  rw [dNext_eq (i' := n) _ (by simp), prevD_eq (j' := n + 2) _ (by simp)] at hH hK
  simp only [Preadditive.comp_add, SSet.ι_chainComplexMap_f] at hH hK
  simp only [Preadditive.sub_comp, Category.assoc, hH, hK, hside]
  abel

theorem singularPrism_piece_eq_of_agree {X Y : TopCat.{w}}
    {f g p q : X ⟶ Y} (H : TopCat.Homotopy f g) (K : TopCat.Homotopy p q)
    {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (hagree : ∀ (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
      H (t, X.toSSetObjEquiv _ s z) = K (t, X.toSSetObjEquiv _ s z))
    (i : Fin (n + 1)) :
    H.toSSet.toSimplicialObjectHomotopy.h i s =
      K.toSSet.toSimplicialObjectHomotopy.h i s := by
  let prism : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj TopCat.I) _⦋n + 1⦌ :=
    ⟨(TopCat.toSSet.obj X).σ i s,
      SSet.stdSimplex.toSSetObjI.app _ (SSet.stdSimplex.objMk₁ i.succ.castSucc)⟩
  let productSimplex := (Functor.LaxMonoidal.μ TopCat.toSSet X TopCat.I).app _ prism
  have hprojection : (TopCat.toSSet.map (fst X TopCat.I)).app _ productSimplex =
      (TopCat.toSSet.obj X).σ i s :=
    congrArg (fun k => k.app _ prism)
      (Functor.Monoidal.μ_fst (F := TopCat.toSSet) X TopCat.I)
  change (TopCat.toSSet.map H.h).app _ productSimplex =
    (TopCat.toSSet.map K.h).app _ productSimplex
  refine (Y.toSSetObjEquiv _).injective (ContinuousMap.ext (fun z => ?_))
  have hspace := congrArg (fun c => X.toSSetObjEquiv _ c z) hprojection
  change ((X ⊗ TopCat.I).toSSetObjEquiv _ productSimplex z).1 =
    X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).σ i s) z at hspace
  rw [TopCat.toSSetObjEquiv_σ_apply] at hspace
  change H (TopCat.I.homeomorph ((X ⊗ TopCat.I).toSSetObjEquiv _ productSimplex z).2,
      ((X ⊗ TopCat.I).toSSetObjEquiv _ productSimplex z).1) =
    K (TopCat.I.homeomorph ((X ⊗ TopCat.I).toSSetObjEquiv _ productSimplex z).2,
      ((X ⊗ TopCat.I).toSSetObjEquiv _ productSimplex z).1)
  rw [hspace]
  exact hagree _ _

theorem singularPrism_boundary_of_constant_faces (R : C) {X Y : TopCat.{w}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (y : Y)
    (hface : ∀ (i : Fin (n + 2)) (t : unitInterval)
      (z : stdSimplex ℝ (Fin (n + 1))),
      H (t, X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i s) z) = y) :
    ∃ b : R ⟶ ((TopCat.toSSet.obj Y).chainComplex R).X (n + 2),
      (TopCat.toSSet.obj Y).ιChainComplex ((TopCat.toSSet.map f).app _ s) -
        (TopCat.toSSet.obj Y).ιChainComplex ((TopCat.toSSet.map g).app _ s) =
          b ≫ ((TopCat.toSSet.obj Y).chainComplex R).d (n + 2) (n + 1) := by
  let K : TopCat.Homotopy (TopCat.const (X := X) y) (TopCat.const (X := X) y) :=
    TopCat.Homotopy.refl _
  have hpieces (i : Fin (n + 2)) (j : Fin (n + 1)) :
      H.toSSet.toSimplicialObjectHomotopy.h j ((TopCat.toSSet.obj X).δ i s) =
        K.toSSet.toSimplicialObjectHomotopy.h j ((TopCat.toSSet.obj X).δ i s) := by
    apply singularPrism_piece_eq_of_agree
    intro time z
    exact hface i time z
  refine ⟨(TopCat.toSSet.obj X).ιChainComplex s ≫
      (H.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom (n + 1) (n + 2) -
    (TopCat.toSSet.obj X).ιChainComplex s ≫
      (K.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom (n + 1) (n + 2), ?_⟩
  simpa only [sub_self, sub_zero] using
    (simplicialPrism_difference_boundary R H.toSSet.toSimplicialObjectHomotopy
      K.toSSet.toSimplicialObjectHomotopy s hpieces).symm

end PoincareConjecture.Proofs.M02
