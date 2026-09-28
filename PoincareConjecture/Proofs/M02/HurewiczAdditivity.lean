import PoincareConjecture.Proofs.M02.HurewiczMap

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial Topology unitInterval

universe w v u

namespace PoincareConjecture.Proofs.M02

theorem exists_genLoop_transAt_paired_homotopies
    {N X : Type*} [DecidableEq N] [TopologicalSpace X] {x : X}
    (i : N) (p q : GenLoop N X x) :
    ∃ H : ContinuousMap.Homotopy p.val (GenLoop.transAt i p q).val,
      ∃ K : ContinuousMap.Homotopy (GenLoop.const : GenLoop N X x).val q.val,
        ∀ (t : unitInterval) (u : I^N), u ∈ Cube.boundary N →
          H (t, u) = K (t, u) := by
  let r := GenLoop.transAt i p q
  let half : unitInterval → unitInterval := fun t =>
    ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hcont : Continuous half := by unfold half; fun_prop
  have hone : half 1 = 1 := by apply Subtype.ext; norm_num [half]
  have hstart (u : I^N) : r (Function.update u i (half 0 * u i)) = p u := by
    have hle : ((half 0 * u i : unitInterval) : ℝ) ≤ 1 / 2 := by
      change ((1 + (0 : ℝ)) / 2) * (u i : ℝ) ≤ 1 / 2
      linarith [(u i).property.2]
    have hscale : (2 : ℝ) * ((half 0 * u i : unitInterval) : ℝ) = (u i : ℝ) := by
      change 2 * (((1 + (0 : ℝ)) / 2) * (u i : ℝ)) = (u i : ℝ)
      ring
    have hclamp : Set.projIcc 0 1 zero_le_one
        (2 * ((half 0 * u i : unitInterval) : ℝ)) = u i := by
      rw [hscale, Set.projIcc_val]
    simp only [r, GenLoop.transAt, GenLoop.coe_copy, Function.update_self]
    rw [if_pos hle, hclamp]
    simp only [Function.update_idem, Function.update_eq_self]
  have htrace (u : I^N) (t : unitInterval) :
      r (Function.update u i (half t)) = q (Function.update u i t) := by
    simp only [r, GenLoop.transAt, GenLoop.coe_copy, Function.update_self]
    split_ifs with hle
    · have ht : t = 0 := by
        apply Subtype.ext
        change (1 + (t : ℝ)) / 2 ≤ 1 / 2 at hle
        change (t : ℝ) = 0
        linarith [t.property.1]
      subst t
      have hclamp : Set.projIcc 0 1 zero_le_one (2 * (half 0 : ℝ)) =
          (1 : unitInterval) := by norm_num [half]
      rw [hclamp]
      exact (GenLoop.boundary p _ ⟨i, Or.inr (by simp)⟩).trans
        (GenLoop.boundary q _ ⟨i, Or.inl (by simp)⟩).symm
    · have hscale : (2 : ℝ) * (half t : ℝ) - 1 = (t : ℝ) := by
        change 2 * ((1 + (t : ℝ)) / 2) - 1 = (t : ℝ)
        ring
      have hclamp : Set.projIcc 0 1 zero_le_one (2 * (half t : ℝ) - 1) = t := by
        rw [hscale, Set.projIcc_val]
      rw [hclamp, Function.update_idem]
  let H : ContinuousMap.Homotopy p.val r.val := {
    toFun := fun z => r (Function.update z.2 i (half z.1 * z.2 i))
    continuous_toFun := r.val.continuous.comp
      (continuous_snd.update i ((hcont.comp continuous_fst).mul
        ((continuous_apply i).comp continuous_snd)))
    map_zero_left := hstart
    map_one_left := fun u => by
      simp only [hone, one_mul, Function.update_eq_self]
      rfl
  }
  let K : ContinuousMap.Homotopy (GenLoop.const : GenLoop N X x).val q.val := {
    toFun := fun z => q (Function.update z.2 i (z.1 * z.2 i))
    continuous_toFun := q.val.continuous.comp
      (continuous_snd.update i (continuous_fst.mul
        ((continuous_apply i).comp continuous_snd)))
    map_zero_left := fun u => by
      simp only [zero_mul]
      exact GenLoop.boundary q _ ⟨i, Or.inl (by simp)⟩
    map_one_left := fun u => by
      simp only [one_mul, Function.update_eq_self]
      rfl
  }
  refine ⟨H, K, ?_⟩
  rintro t u ⟨j, hj⟩
  change r (Function.update u i (half t * u i)) = q (Function.update u i (t * u i))
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · rw [hj, mul_zero, mul_zero]
      exact (GenLoop.boundary r _ ⟨i, Or.inl (by simp)⟩).trans
        (GenLoop.boundary q _ ⟨i, Or.inl (by simp)⟩).symm
    · rw [hj, mul_one, mul_one]
      exact htrace u t
  · exact (GenLoop.boundary r _ ⟨j, by simpa only [Function.update_of_ne hji] using hj⟩).trans
      (GenLoop.boundary q _ ⟨j, by simpa only [Function.update_of_ne hji] using hj⟩).symm

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

theorem singularSimplexHomologyClass_sub_eq_of_paired_homotopies (R : C)
    {A X : TopCat.{w}} {f g p q : A ⟶ X}
    (H : TopCat.Homotopy f g) (K : TopCat.Homotopy p q) {n : ℕ}
    (s : (TopCat.toSSet.obj A) _⦋n + 1⦌) (x : X)
    (hf : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map f).app _ s) =
        singularConstantSimplex X n x)
    (hg : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map g).app _ s) =
        singularConstantSimplex X n x)
    (hp : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map p).app _ s) =
        singularConstantSimplex X n x)
    (hq : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map q).app _ s) =
        singularConstantSimplex X n x)
    (hboundary : ∀ (i : Fin (n + 2)) (t : unitInterval)
      (z : stdSimplex ℝ (Fin (n + 1))),
      H (t, A.toSSetObjEquiv _ ((TopCat.toSSet.obj A).δ i s) z) =
        K (t, A.toSSetObjEquiv _ ((TopCat.toSSet.obj A).δ i s) z)) :
    singularSimplexHomologyClass R X ((TopCat.toSSet.map f).app _ s) x hf -
      singularSimplexHomologyClass R X ((TopCat.toSSet.map g).app _ s) x hg =
    singularSimplexHomologyClass R X ((TopCat.toSSet.map p).app _ s) x hp -
      singularSimplexHomologyClass R X ((TopCat.toSSet.map q).app _ s) x hq := by
  let Y := TopCat.toSSet.obj X
  let b := (TopCat.toSSet.obj A).ιChainComplex s ≫
      (H.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom (n + 1) (n + 2) -
    (TopCat.toSSet.obj A).ιChainComplex s ≫
      (K.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom (n + 1) (n + 2)
  have hb := simplicialPrism_difference_boundary R
    H.toSSet.toSimplicialObjectHomotopy K.toSSet.toSimplicialObjectHomotopy s
    (fun i j => singularPrism_piece_eq_of_agree H K
      ((TopCat.toSSet.obj A).δ i s) (hboundary i) j)
  let L (a : A ⟶ X) (ha : ∀ i : Fin (n + 2),
      Y.δ i ((TopCat.toSSet.map a).app _ s) = singularConstantSimplex X n x) :=
    (Y.chainComplex R).liftCycles
      (Y.ιChainComplex ((TopCat.toSSet.map a).app _ s) -
        Y.ιChainComplex (singularConstantSimplex X (n + 1) x)) n (by simp)
      (singularSimplexDifference_d_eq_zero R X _ x ha)
  have hlift : (L f hf - L g hg) - (L p hp - L q hq) =
      b ≫ (Y.chainComplex R).toCycles (n + 2) (n + 1) := by
    apply (cancel_mono ((Y.chainComplex R).iCycles (n + 1))).mp
    simp only [L, Preadditive.sub_comp, HomologicalComplex.liftCycles_i,
      Category.assoc, HomologicalComplex.toCycles_i]
    rw [hb]
    abel
  change L f hf ≫ (Y.chainComplex R).homologyπ (n + 1) -
      L g hg ≫ (Y.chainComplex R).homologyπ (n + 1) =
    L p hp ≫ (Y.chainComplex R).homologyπ (n + 1) -
      L q hq ≫ (Y.chainComplex R).homologyπ (n + 1)
  apply sub_eq_zero.mp
  simp only [← Preadditive.sub_comp]
  rw [hlift, Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, comp_zero]

theorem genLoopSingularHomologyClass_transAt (R : C) (X : TopCat.{w})
    {n : ℕ} {x : X} (i : Fin (n + 1)) (p q : GenLoop (Fin (n + 1)) X x) :
    genLoopSingularHomologyClass R X (GenLoop.transAt i p q) =
      genLoopSingularHomologyClass R X p + genLoopSingularHomologyClass R X q := by
  obtain ⟨H, K, htrace⟩ := exists_genLoop_transAt_paired_homotopies i p q
  let r := GenLoop.transAt i p q
  let D : TopCat.{w} := SimplexCategory.toTop.obj ⦋n + 1⦌
  let s : (TopCat.toSSet.obj D) _⦋n + 1⦌ := ⟨𝟙 D⟩
  let e := Classical.choose (exists_stdSimplex_cube_pair_homeomorph (n + 1))
  let eD : C(D, I^(Fin (n + 1))) :=
    ⟨fun z => e z.down, e.continuous.comp Homeomorph.ulift.continuous⟩
  let lift (a : GenLoop (Fin (n + 1)) X x) : D ⟶ X := (genLoopSingularSimplex X a).down
  let H' : TopCat.Homotopy (lift p) (lift r) := H.compContinuousMap eD
  let K' : TopCat.Homotopy (lift GenLoop.const) (lift q) := K.compContinuousMap eD
  have himage (a : GenLoop (Fin (n + 1)) X x) :
      (TopCat.toSSet.map (lift a)).app _ s = genLoopSingularSimplex X a :=
    ULift.ext _ _ (Category.id_comp (lift a))
  have hboundary (j : Fin (n + 2)) (time : unitInterval)
      (z : stdSimplex ℝ (Fin (n + 1))) :
      H' (time, D.toSSetObjEquiv _ ((TopCat.toSSet.obj D).δ j s) z) =
        K' (time, D.toSSetObjEquiv _ ((TopCat.toSSet.obj D).δ j s) z) := by
    change H (time, e (stdSimplex.map j.succAbove z)) =
      K (time, e (stdSimplex.map j.succAbove z))
    apply htrace time
    apply (Classical.choose_spec (exists_stdSimplex_cube_pair_homeomorph (n + 1)) _).mp
    refine ⟨j, ?_⟩
    change FunOnFinite.linearMap ℝ ℝ j.succAbove (z : Fin (n + 1) → ℝ) j = 0
    simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_ne]
  have hclasses := singularSimplexHomologyClass_sub_eq_of_paired_homotopies R H' K' s x
    (fun j => by rw [himage]; exact genLoopSingularSimplex_face X p j)
    (fun j => by rw [himage]; exact genLoopSingularSimplex_face X r j)
    (fun j => by rw [himage]; exact genLoopSingularSimplex_face X GenLoop.const j)
    (fun j => by rw [himage]; exact genLoopSingularSimplex_face X q j) hboundary
  have hdiff : genLoopSingularHomologyClass R X p - genLoopSingularHomologyClass R X r =
      -genLoopSingularHomologyClass R X q := by
    simpa only [himage, genLoopSingularSimplex_const, singularSimplexHomologyClass_const,
      genLoopSingularHomologyClass, zero_sub] using hclasses
  simpa only [sub_sub_cancel, sub_neg_eq_add] using
    congrArg (fun z => genLoopSingularHomologyClass R X p - z) hdiff

theorem homotopyGroupSingularHomologyMap_mul (R : C) (X : TopCat.{w})
    (n : ℕ) (x : X) (a b : HomotopyGroup.Pi (n + 1) X x) :
    homotopyGroupSingularHomologyMap R X n x (a * b) =
      homotopyGroupSingularHomologyMap R X n x a +
        homotopyGroupSingularHomologyMap R X n x b := by
  refine Quotient.inductionOn₂ a b (fun p q => ?_)
  let p' : HomotopyGroup.Pi (n + 1) X x := ⟦p⟧
  let q' : HomotopyGroup.Pi (n + 1) X x := ⟦q⟧
  change homotopyGroupSingularHomologyMap R X n x (p' * q') =
    homotopyGroupSingularHomologyMap R X n x p' +
      homotopyGroupSingularHomologyMap R X n x q'
  have hmul : p' * q' =
      (⟦GenLoop.transAt (0 : Fin (n + 1)) q p⟧ : HomotopyGroup.Pi (n + 1) X x) := by
    dsimp [p', q']
    exact HomotopyGroup.mul_spec (i := (0 : Fin (n + 1)))
  rw [hmul]
  simp only [p', q', homotopyGroupSingularHomologyMap_mk,
    genLoopSingularHomologyClass_transAt]
  exact add_comm _ _

noncomputable def homotopyGroupSingularHomologyHom (R : C) (X : TopCat.{w})
    (n : ℕ) (x : X) :
    HomotopyGroup.Pi (n + 1) X x →*
      Multiplicative (R ⟶ (TopCat.toSSet.obj X).homology R (n + 1)) where
  toFun a := Multiplicative.ofAdd (homotopyGroupSingularHomologyMap R X n x a)
  map_one' := congrArg Multiplicative.ofAdd (homotopyGroupSingularHomologyMap_one R X n x)
  map_mul' a b :=
    congrArg Multiplicative.ofAdd (homotopyGroupSingularHomologyMap_mul R X n x a b)

end PoincareConjecture.Proofs.M02
