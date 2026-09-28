import PoincareConjecture.Proofs.M02.SingularPrism

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe w v u

namespace PoincareConjecture.Proofs.M02

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

noncomputable def simplicialSimplexDifferenceHomologyClass (R : C) (X : SSet.{w})
    {n : ℕ} (s t : X _⦋n + 1⦌)
    (hface : ∀ i : Fin (n + 2), X.δ i s = X.δ i t) :
    R ⟶ X.homology R (n + 1) :=
  (X.chainComplex R).liftCycles (X.ιChainComplex s - X.ιChainComplex t) n (by simp)
    (simplicialSimplexDifference_d_eq_zero R X s t hface) ≫
      (X.chainComplex R).homologyπ (n + 1)

theorem simplicialSimplexDifferenceHomologyClass_naturality (R : C)
    {X Y : SSet.{w}} (f : X ⟶ Y) {n : ℕ} (s t : X _⦋n + 1⦌)
    (hface : ∀ i : Fin (n + 2), X.δ i s = X.δ i t) :
    simplicialSimplexDifferenceHomologyClass R X s t hface ≫
      SSet.homologyMap f R (n + 1) =
        simplicialSimplexDifferenceHomologyClass R Y (f.app _ s) (f.app _ t)
          (fun i => by rw [← SSet.δ_naturality_apply, ← SSet.δ_naturality_apply, hface]) := by
  unfold simplicialSimplexDifferenceHomologyClass SSet.homologyMap
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  simp only [Preadditive.sub_comp, SSet.ι_chainComplexMap_f]

theorem simplicialSimplexDifferenceHomologyClass_eq_of_boundary (R : C)
    (X : SSet.{w}) {n : ℕ} (s t s' t' : X _⦋n + 1⦌)
    (hface : ∀ i : Fin (n + 2), X.δ i s = X.δ i t)
    (hface' : ∀ i : Fin (n + 2), X.δ i s' = X.δ i t')
    (b : R ⟶ (X.chainComplex R).X (n + 2))
    (hb : (X.ιChainComplex s - X.ιChainComplex t) -
      (X.ιChainComplex s' - X.ιChainComplex t') =
        b ≫ (X.chainComplex R).d (n + 2) (n + 1)) :
    simplicialSimplexDifferenceHomologyClass R X s t hface =
      simplicialSimplexDifferenceHomologyClass R X s' t' hface' := by
  let z := (X.chainComplex R).liftCycles (X.ιChainComplex s - X.ιChainComplex t) n
    (by simp) (simplicialSimplexDifference_d_eq_zero R X s t hface)
  let z' := (X.chainComplex R).liftCycles (X.ιChainComplex s' - X.ιChainComplex t') n
    (by simp) (simplicialSimplexDifference_d_eq_zero R X s' t' hface')
  have hlift : z - z' = b ≫ (X.chainComplex R).toCycles (n + 2) (n + 1) := by
    apply (cancel_mono ((X.chainComplex R).iCycles (n + 1))).mp
    simpa only [z, z', Preadditive.sub_comp, HomologicalComplex.liftCycles_i,
      Category.assoc, HomologicalComplex.toCycles_i] using hb
  change z ≫ _ = z' ≫ _
  apply sub_eq_zero.mp
  rw [← Preadditive.sub_comp, hlift, Category.assoc,
    HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

noncomputable def singularSimplexHomologyClass (R : C) (X : TopCat.{w})
    {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (x : X)
    (hface : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x) :
    R ⟶ (TopCat.toSSet.obj X).homology R (n + 1) :=
  simplicialSimplexDifferenceHomologyClass R (TopCat.toSSet.obj X) s
    (singularConstantSimplex X (n + 1) x)
    (fun i => (hface i).trans (singularConstantSimplex_face X x i).symm)

theorem singularSimplexHomologyClass_eq_of_homotopy (R : C) {X Y : TopCat.{w}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (y : Y)
    (hf : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj Y).δ i ((TopCat.toSSet.map f).app _ s) =
        singularConstantSimplex Y n y)
    (hg : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj Y).δ i ((TopCat.toSSet.map g).app _ s) =
        singularConstantSimplex Y n y)
    (hface : ∀ (i : Fin (n + 2)) (t : unitInterval)
      (z : stdSimplex ℝ (Fin (n + 1))),
      H (t, X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i s) z) = y) :
    singularSimplexHomologyClass R Y ((TopCat.toSSet.map f).app _ s) y hf =
      singularSimplexHomologyClass R Y ((TopCat.toSSet.map g).app _ s) y hg := by
  obtain ⟨b, hb⟩ := singularPrism_boundary_of_constant_faces R H s y hface
  unfold singularSimplexHomologyClass
  apply simplicialSimplexDifferenceHomologyClass_eq_of_boundary R _ _ _ _ _ _ _ b
  rw [← hb]
  abel

theorem singularSimplexHomologyClass_naturality (R : C) {X Y : TopCat.{w}}
    (f : X ⟶ Y) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (x : X)
    (hface : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x) :
    singularSimplexHomologyClass R X s x hface ≫
      SSet.homologyMap (TopCat.toSSet.map f) R (n + 1) =
        singularSimplexHomologyClass R Y ((TopCat.toSSet.map f).app _ s) (f x)
          (fun i => by
            rw [← SSet.δ_naturality_apply, hface, singularConstantSimplex_map]) := by
  unfold singularSimplexHomologyClass
  simpa only [singularConstantSimplex_map] using
    simplicialSimplexDifferenceHomologyClass_naturality R (TopCat.toSSet.map f)
      s (singularConstantSimplex X (n + 1) x)
      (fun i => (hface i).trans (singularConstantSimplex_face X x i).symm)

theorem singularSimplexHomologyClass_const (R : C) (X : TopCat.{w})
    {n : ℕ} (x : X) :
    singularSimplexHomologyClass R X (singularConstantSimplex X (n + 1) x) x
      (singularConstantSimplex_face X x) = 0 := by
  have hlift : ((TopCat.toSSet.obj X).chainComplex R).liftCycles
      (0 : R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X (n + 1)) n
      (by simp) (by simp) = 0 := by
    apply (cancel_mono (((TopCat.toSSet.obj X).chainComplex R).iCycles (n + 1))).mp
    simp only [HomologicalComplex.liftCycles_i, zero_comp]
  simp only [singularSimplexHomologyClass, simplicialSimplexDifferenceHomologyClass,
    sub_self, hlift, zero_comp]

theorem singularSimplexHomologyClass_eq_of_simplex_homotopy (R : C) (X : TopCat.{w})
    {n : ℕ} (s t : (TopCat.toSSet.obj X) _⦋n + 1⦌) (x : X)
    (hs : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i s = singularConstantSimplex X n x)
    (ht : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i t = singularConstantSimplex X n x)
    (H : ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ t))
    (hboundary : ∀ (i : Fin (n + 2)) (time : unitInterval)
      (z : stdSimplex ℝ (Fin (n + 1))), H (time, stdSimplex.map i.succAbove z) = x) :
    singularSimplexHomologyClass R X s x hs = singularSimplexHomologyClass R X t x ht := by
  let D : TopCat.{w} := SimplexCategory.toTop.obj ⦋n + 1⦌
  let identitySimplex : (TopCat.toSSet.obj D) _⦋n + 1⦌ := ⟨𝟙 D⟩
  let liftedHomotopy : TopCat.Homotopy (s.down : D ⟶ X) (t.down : D ⟶ X) :=
    H.compContinuousMap ⟨Homeomorph.ulift, Homeomorph.ulift.continuous⟩
  have hleft : (TopCat.toSSet.map s.down).app _ identitySimplex = s :=
    ULift.ext _ _ (Category.id_comp s.down)
  have hright : (TopCat.toSSet.map t.down).app _ identitySimplex = t :=
    ULift.ext _ _ (Category.id_comp t.down)
  have hclass := singularSimplexHomologyClass_eq_of_homotopy R liftedHomotopy
    identitySimplex x (fun i => by rw [hleft]; exact hs i)
    (fun i => by rw [hright]; exact ht i) (fun i time z => hboundary i time z)
  simpa only [hleft, hright] using hclass

end PoincareConjecture.Proofs.M02
