import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Subdivision.SingularPrism








set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

universe w v u

namespace Poincare.Topology


theorem singularPrism_piece_eq_of_two_source_agree {A B X : TopCat.{w}}
    {f g : A ⟶ X} {p q : B ⟶ X} (H : TopCat.Homotopy f g) (K : TopCat.Homotopy p q)
    {n : ℕ} (s : (TopCat.toSSet.obj A) _⦋n⦌) (r : (TopCat.toSSet.obj B) _⦋n⦌)
    (hagree : ∀ (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
      H (t, A.toSSetObjEquiv _ s z) = K (t, B.toSSetObjEquiv _ r z))
    (i : Fin (n + 1)) :
    H.toSSet.toSimplicialObjectHomotopy.h i s =
      K.toSSet.toSimplicialObjectHomotopy.h i r := by
  let timeSimplex : (TopCat.toSSet.obj TopCat.I) _⦋n + 1⦌ :=
    SSet.stdSimplex.toSSetObjI.app _ (SSet.stdSimplex.objMk₁ i.succ.castSucc)
  let prismA : (TopCat.toSSet.obj A ⊗ TopCat.toSSet.obj TopCat.I) _⦋n + 1⦌ :=
    ⟨(TopCat.toSSet.obj A).σ i s, timeSimplex⟩
  let prismB : (TopCat.toSSet.obj B ⊗ TopCat.toSSet.obj TopCat.I) _⦋n + 1⦌ :=
    ⟨(TopCat.toSSet.obj B).σ i r, timeSimplex⟩
  let productA := (Functor.LaxMonoidal.μ TopCat.toSSet A TopCat.I).app _ prismA
  let productB := (Functor.LaxMonoidal.μ TopCat.toSSet B TopCat.I).app _ prismB
  have hAfst : (TopCat.toSSet.map (fst A TopCat.I)).app _ productA =
      (TopCat.toSSet.obj A).σ i s :=
    congrArg (fun k => k.app _ prismA)
      (Functor.Monoidal.μ_fst (F := TopCat.toSSet) A TopCat.I)
  have hBfst : (TopCat.toSSet.map (fst B TopCat.I)).app _ productB =
      (TopCat.toSSet.obj B).σ i r :=
    congrArg (fun k => k.app _ prismB)
      (Functor.Monoidal.μ_fst (F := TopCat.toSSet) B TopCat.I)
  have hAsnd : (TopCat.toSSet.map (snd A TopCat.I)).app _ productA = timeSimplex :=
    congrArg (fun k => k.app _ prismA)
      (Functor.Monoidal.μ_snd (F := TopCat.toSSet) A TopCat.I)
  have hBsnd : (TopCat.toSSet.map (snd B TopCat.I)).app _ productB = timeSimplex :=
    congrArg (fun k => k.app _ prismB)
      (Functor.Monoidal.μ_snd (F := TopCat.toSSet) B TopCat.I)
  change (TopCat.toSSet.map H.h).app _ productA = (TopCat.toSSet.map K.h).app _ productB
  refine (X.toSSetObjEquiv _).injective (ContinuousMap.ext (fun z => ?_))
  have hspaceA := congrArg (fun c => A.toSSetObjEquiv _ c z) hAfst
  have hspaceB := congrArg (fun c => B.toSSetObjEquiv _ c z) hBfst
  have htimeA := congrArg (fun c => TopCat.I.toSSetObjEquiv _ c z) hAsnd
  have htimeB := congrArg (fun c => TopCat.I.toSSetObjEquiv _ c z) hBsnd
  change ((A ⊗ TopCat.I).toSSetObjEquiv _ productA z).1 =
    A.toSSetObjEquiv _ ((TopCat.toSSet.obj A).σ i s) z at hspaceA
  change ((B ⊗ TopCat.I).toSSetObjEquiv _ productB z).1 =
    B.toSSetObjEquiv _ ((TopCat.toSSet.obj B).σ i r) z at hspaceB
  change ((A ⊗ TopCat.I).toSSetObjEquiv _ productA z).2 =
    TopCat.I.toSSetObjEquiv _ timeSimplex z at htimeA
  change ((B ⊗ TopCat.I).toSSetObjEquiv _ productB z).2 =
    TopCat.I.toSSetObjEquiv _ timeSimplex z at htimeB
  change H (TopCat.I.homeomorph ((A ⊗ TopCat.I).toSSetObjEquiv _ productA z).2,
      ((A ⊗ TopCat.I).toSSetObjEquiv _ productA z).1) =
    K (TopCat.I.homeomorph ((B ⊗ TopCat.I).toSSetObjEquiv _ productB z).2,
      ((B ⊗ TopCat.I).toSSetObjEquiv _ productB z).1)
  rw [hspaceA, hspaceB, htimeA, htimeB,
    TopCat.toSSetObjEquiv_σ_apply, TopCat.toSSetObjEquiv_σ_apply]
  exact hagree _ _

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]


noncomputable def singularSimplexPrism (R : C) (X : TopCat.{w}) {n : ℕ}
    {s t : (TopCat.toSSet.obj X) _⦋n⦌}
    (H : ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ t)) :
    R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) :=
  let D : TopCat.{w} := SimplexCategory.toTop.obj ⦋n⦌
  let H' : TopCat.Homotopy s.down t.down :=
    H.compContinuousMap ⟨Homeomorph.ulift, Homeomorph.ulift.continuous⟩
  (TopCat.toSSet.obj D).ιChainComplex (⟨𝟙 D⟩ : (TopCat.toSSet.obj D) _⦋n⦌) ≫
    (H'.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom n (n + 1)


theorem singularSimplexPrism_boundary (R : C) (X : TopCat.{w}) {n : ℕ}
    {s t : (TopCat.toSSet.obj X) _⦋n + 1⦌}
    (H : ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ t))
    (h : ∀ i : Fin (n + 2), ContinuousMap.Homotopy
      (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i s))
      (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i t)))
    (hface : ∀ (i : Fin (n + 2)) (a : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
      H (a, stdSimplex.map i.succAbove z) = h i (a, z)) :
    singularSimplexPrism R X H ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) +
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • singularSimplexPrism R X (h i) =
        (TopCat.toSSet.obj X).ιChainComplex s - (TopCat.toSSet.obj X).ιChainComplex t := by
  let D : TopCat.{w} := SimplexCategory.toTop.obj ⦋n + 1⦌
  let E : TopCat.{w} := SimplexCategory.toTop.obj ⦋n⦌
  let idD : (TopCat.toSSet.obj D) _⦋n + 1⦌ := ⟨𝟙 D⟩
  let idE : (TopCat.toSSet.obj E) _⦋n⦌ := ⟨𝟙 E⟩
  let f : D ⟶ X := s.down
  let g : D ⟶ X := t.down
  let H' : TopCat.Homotopy f g :=
    H.compContinuousMap ⟨Homeomorph.ulift, Homeomorph.ulift.continuous⟩
  let K (i : Fin (n + 2)) : TopCat.Homotopy ((TopCat.toSSet.obj X).δ i s).down
      ((TopCat.toSSet.obj X).δ i t).down :=
    (h i).compContinuousMap ⟨Homeomorph.ulift, Homeomorph.ulift.continuous⟩
  have hpiece (i : Fin (n + 2)) (j : Fin (n + 1)) :
      H'.toSSet.toSimplicialObjectHomotopy.h j ((TopCat.toSSet.obj D).δ i idD) =
        (K i).toSSet.toSimplicialObjectHomotopy.h j idE := by
    apply singularPrism_piece_eq_of_two_source_agree
    intro a z
    exact hface i a z
  have hfacePrism (i : Fin (n + 2)) :
      (TopCat.toSSet.obj D).ιChainComplex ((TopCat.toSSet.obj D).δ i idD) ≫
        (H'.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom n (n + 1) =
      singularSimplexPrism R X (h i) := by
    change _ = (TopCat.toSSet.obj E).ιChainComplex idE ≫
      ((K i).toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom n (n + 1)
    simp only [simplicialPrism_onSimplex]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact congrArg (fun a => (-1 : ℤ) ^ j.val •
      (TopCat.toSSet.obj X).ιChainComplex (R := R) a) (hpiece i j)
  have hside : (TopCat.toSSet.obj D).ιChainComplex idD ≫
      ((TopCat.toSSet.obj D).chainComplex R).d (n + 1) n ≫
        (H'.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • singularSimplexPrism R X (h i) := by
    simp only [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp,
      Preadditive.zsmul_comp, hfacePrism]
  have hcomm := congrArg (fun a => (TopCat.toSSet.obj D).ιChainComplex idD ≫ a)
    ((H'.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).comm (n + 1))
  rw [dNext_eq (i' := n) _ (by simp), prevD_eq (j' := n + 2) _ (by simp)] at hcomm
  simp only [Preadditive.comp_add, SSet.ι_chainComplexMap_f] at hcomm
  have hs : (TopCat.toSSet.map f).app _ idD = s := by
    apply ULift.ext
    exact Category.id_comp f
  have ht : (TopCat.toSSet.map g).app _ idD = t := by
    apply ULift.ext
    exact Category.id_comp g
  rw [hs, ht, hside] at hcomm
  change ((TopCat.toSSet.obj D).ιChainComplex idD ≫
      (H'.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom (n + 1) (n + 2)) ≫
    ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) + _ = _
  rw [Category.assoc, hcomm]
  abel


noncomputable def singularSimplexFamilyMap (R : C) (X : TopCat.{w}) {n : ℕ}
    (r : (TopCat.toSSet.obj X) _⦋n⦌ → (TopCat.toSSet.obj X) _⦋n⦌) :
    ((TopCat.toSSet.obj X).chainComplex R).X n ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n :=
  Sigma.desc fun s => (TopCat.toSSet.obj X).ιChainComplex (r s)


noncomputable def singularSimplexFamilyPrism (R : C) (X : TopCat.{w}) {n : ℕ}
    (r : (TopCat.toSSet.obj X) _⦋n⦌ → (TopCat.toSSet.obj X) _⦋n⦌)
    (H : ∀ s, ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ (r s))) :
    ((TopCat.toSSet.obj X).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) :=
  Sigma.desc fun s => singularSimplexPrism R X (H s)


theorem singularSimplexFamilyPrism_boundary (R : C) (X : TopCat.{w}) {n : ℕ}
    (r : (TopCat.toSSet.obj X) _⦋n + 1⦌ → (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (r0 : (TopCat.toSSet.obj X) _⦋n⦌ → (TopCat.toSSet.obj X) _⦋n⦌)
    (H : ∀ s, ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ (r s)))
    (K : ∀ s, ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ (r0 s)))
    (hface : ∀ (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2))
      (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
      H s (t, stdSimplex.map i.succAbove z) = K ((TopCat.toSSet.obj X).δ i s) (t, z)) :
    singularSimplexFamilyPrism R X r H ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) +
      ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫
        singularSimplexFamilyPrism R X r0 K =
      𝟙 _ - singularSimplexFamilyMap R X r := by
  apply SSet.chainComplex_hom_ext
  intro s
  have htarget (i : Fin (n + 2)) :
      X.toSSetObjEquiv _ (r0 ((TopCat.toSSet.obj X).δ i s)) =
        X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i (r s)) := by
    ext z
    rw [TopCat.toSSetObjEquiv_δ_apply]
    exact ((K ((TopCat.toSSet.obj X).δ i s)).apply_one z).symm.trans
      ((hface s i 1 z).symm.trans ((H s).apply_one (stdSimplex.map i.succAbove z)))
  let K' (i : Fin (n + 2)) := (K ((TopCat.toSSet.obj X).δ i s)).cast rfl (htarget i)
  have hcast (i : Fin (n + 2)) : singularSimplexPrism R X (K' i) =
      singularSimplexPrism R X (K ((TopCat.toSSet.obj X).δ i s)) := rfl
  have hb := singularSimplexPrism_boundary R X (H s) K' (hface s)
  simp only [hcast] at hb
  have htop : (TopCat.toSSet.obj X).ιChainComplex s ≫
      singularSimplexFamilyPrism R X r H = singularSimplexPrism R X (H s) := by
    exact Sigma.ι_desc (fun a => singularSimplexPrism R X (H a)) s
  have hlower (a : (TopCat.toSSet.obj X) _⦋n⦌) : (TopCat.toSSet.obj X).ιChainComplex a ≫
      singularSimplexFamilyPrism R X r0 K = singularSimplexPrism R X (K a) := by
    exact Sigma.ι_desc (fun b => singularSimplexPrism R X (K b)) a
  have hmap : (TopCat.toSSet.obj X).ιChainComplex s ≫ singularSimplexFamilyMap R X r =
      (TopCat.toSSet.obj X).ιChainComplex (r s) := by
    exact Sigma.ι_desc (fun a => (TopCat.toSSet.obj X).ιChainComplex (r a)) s
  simpa only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, htop, SSet.ιChainComplex_d, Preadditive.sum_comp,
    Preadditive.zsmul_comp, hlower, hmap] using hb


theorem singularSimplexFamily_cycle_difference_boundary (R : C) (X : TopCat.{w}) {n : ℕ}
    (r : (TopCat.toSSet.obj X) _⦋n + 1⦌ → (TopCat.toSSet.obj X) _⦋n + 1⦌)
    (r0 : (TopCat.toSSet.obj X) _⦋n⦌ → (TopCat.toSSet.obj X) _⦋n⦌)
    (H : ∀ s, ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ (r s)))
    (K : ∀ s, ContinuousMap.Homotopy (X.toSSetObjEquiv _ s) (X.toSSetObjEquiv _ (r0 s)))
    (hface : ∀ (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2))
      (t : unitInterval) (z : stdSimplex ℝ (Fin (n + 1))),
      H s (t, stdSimplex.map i.succAbove z) = K ((TopCat.toSSet.obj X).δ i s) (t, z))
    {A : C} (z : A ⟶ ((TopCat.toSSet.obj X).chainComplex R).X (n + 1))
    (hz : z ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n = 0) :
    z - z ≫ singularSimplexFamilyMap R X r =
      (z ≫ singularSimplexFamilyPrism R X r H) ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) := by
  have hb := congrArg (fun a => z ≫ a)
    (singularSimplexFamilyPrism_boundary R X r r0 H K hface)
  simpa only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, hz, zero_comp, add_zero] using hb.symm

end Poincare.Topology
