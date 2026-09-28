import PoincareConjecture.Proofs.M59.Mathlib.CubeTransport
import PoincareConjecture.Proofs.M02.HurewiczMap

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial Topology unitInterval

universe w v u

namespace PoincareConjecture.Proofs.M59

open M02

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

theorem simplexDifferenceHomologyClass_eq_of_paired_homotopies (R : C)
    {A X : TopCat.{w}} {f g p q : A ⟶ X}
    (H : TopCat.Homotopy f g) (K : TopCat.Homotopy p q) {n : ℕ}
    (s : (TopCat.toSSet.obj A) _⦋n + 1⦌)
    (hleft : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map f).app _ s) =
        (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map p).app _ s))
    (hright : ∀ i : Fin (n + 2),
      (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map g).app _ s) =
        (TopCat.toSSet.obj X).δ i ((TopCat.toSSet.map q).app _ s))
    (hboundary : ∀ (i : Fin (n + 2)) (t : unitInterval)
      (z : stdSimplex ℝ (Fin (n + 1))),
      H (t, A.toSSetObjEquiv _ ((TopCat.toSSet.obj A).δ i s) z) =
        K (t, A.toSSetObjEquiv _ ((TopCat.toSSet.obj A).δ i s) z)) :
    simplicialSimplexDifferenceHomologyClass R (TopCat.toSSet.obj X)
      ((TopCat.toSSet.map f).app _ s) ((TopCat.toSSet.map p).app _ s) hleft =
    simplicialSimplexDifferenceHomologyClass R (TopCat.toSSet.obj X)
      ((TopCat.toSSet.map g).app _ s) ((TopCat.toSSet.map q).app _ s) hright := by
  let b := (TopCat.toSSet.obj A).ιChainComplex s ≫
      (H.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom (n + 1) (n + 2) -
    (TopCat.toSSet.obj A).ιChainComplex s ≫
      (K.toSSet.toSimplicialObjectHomotopy.sSetChainComplexMap R).hom (n + 1) (n + 2)
  have hb := simplicialPrism_difference_boundary R
    H.toSSet.toSimplicialObjectHomotopy K.toSSet.toSimplicialObjectHomotopy s
    (fun i j => singularPrism_piece_eq_of_agree H K
      ((TopCat.toSSet.obj A).δ i s) (hboundary i) j)
  apply simplicialSimplexDifferenceHomologyClass_eq_of_boundary R _ _ _ _ _ _ _ b
  rw [hb]
  abel

theorem genLoopSingularHomologyClass_eq_of_homotopyAlong (R : C) (X : TopCat.{w})
    {n : ℕ} {x y : X} {a : GenLoop (Fin (n + 1)) X x}
    {b : GenLoop (Fin (n + 1)) X y} {p : Path x y}
    (H : GenLoop.HomotopyAlong p a b) :
    genLoopSingularHomologyClass R X a = genLoopSingularHomologyClass R X b := by
  let D : TopCat.{w} := SimplexCategory.toTop.obj ⦋n + 1⦌
  let s : (TopCat.toSSet.obj D) _⦋n + 1⦌ := ⟨𝟙 D⟩
  let e := Classical.choose (exists_stdSimplex_cube_pair_homeomorph (n + 1))
  let eD : C(D, I^(Fin (n + 1))) :=
    ⟨fun z => e z.down, e.continuous.comp Homeomorph.ulift.continuous⟩
  let lift {z : X} (c : GenLoop (Fin (n + 1)) X z) : D ⟶ X :=
    (genLoopSingularSimplex X c).down
  let H' : TopCat.Homotopy (lift a) (lift b) := H.toHomotopy.compContinuousMap eD
  let K' : TopCat.Homotopy
      (lift (GenLoop.const : GenLoop (Fin (n + 1)) X x))
      (lift (GenLoop.const : GenLoop (Fin (n + 1)) X y)) :=
    (GenLoop.HomotopyAlong.const (N := Fin (n + 1)) p).toHomotopy.compContinuousMap eD
  have himage {z : X} (c : GenLoop (Fin (n + 1)) X z) :
      (TopCat.toSSet.map (lift c)).app _ s = genLoopSingularSimplex X c :=
    ULift.ext _ _ (Category.id_comp (lift c))
  have hfaces {z : X} (c : GenLoop (Fin (n + 1)) X z) (j : Fin (n + 2)) :
      (TopCat.toSSet.obj X).δ j ((TopCat.toSSet.map (lift c)).app _ s) =
        (TopCat.toSSet.obj X).δ j
          ((TopCat.toSSet.map (lift (GenLoop.const : GenLoop (Fin (n + 1)) X z))).app _ s) := by
    rw [himage, himage, genLoopSingularSimplex_face, genLoopSingularSimplex_face]
  have htrace (j : Fin (n + 2)) (time : unitInterval)
      (z : stdSimplex ℝ (Fin (n + 1))) :
      H' (time, D.toSSetObjEquiv _ ((TopCat.toSSet.obj D).δ j s) z) =
        K' (time, D.toSSetObjEquiv _ ((TopCat.toSSet.obj D).δ j s) z) := by
    change H.toHomotopy (time, e (stdSimplex.map j.succAbove z)) = p time
    apply H.boundary_path time
      ⟨e (stdSimplex.map j.succAbove z), ?_⟩
    apply (Classical.choose_spec (exists_stdSimplex_cube_pair_homeomorph (n + 1)) _).mp
    refine ⟨j, ?_⟩
    change FunOnFinite.linearMap ℝ ℝ j.succAbove (z : Fin (n + 1) → ℝ) j = 0
    simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_ne]
  have heq := simplexDifferenceHomologyClass_eq_of_paired_homotopies R
    H' K' s (hfaces a) (hfaces b) htrace
  simpa only [himage, genLoopSingularSimplex_const,
    genLoopSingularHomologyClass, singularSimplexHomologyClass] using heq

theorem genLoopSingularHomologyClass_boundaryTransport (R : C) (X : TopCat.{w})
    {n : ℕ} {x y : X} (p : Path x y) (a : GenLoop (Fin (n + 1)) X x) :
    genLoopSingularHomologyClass R X (GenLoop.boundaryTransport p a) =
      genLoopSingularHomologyClass R X a :=
  (genLoopSingularHomologyClass_eq_of_homotopyAlong R X
    (GenLoop.boundaryTransportHomotopy p a)).symm

end PoincareConjecture.Proofs.M59
