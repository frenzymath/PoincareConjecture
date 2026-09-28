import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Groups.HomotopyMap
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Simplex.SimplexCube
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Subdivision.SingularHomologyClass








set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial Topology unitInterval

universe w v u

namespace Poincare.Topology


noncomputable def genLoopSingularSimplex (X : TopCat.{w}) {n : ℕ} {x : X}
    (p : GenLoop (Fin n) X x) : (TopCat.toSSet.obj X) _⦋n⦌ :=
  let coordinates := Classical.choose (exists_stdSimplex_cube_pair_homeomorph n)
  (X.toSSetObjEquiv _).symm (p.val.comp ⟨coordinates, coordinates.continuous⟩)


theorem genLoopSingularSimplex_face (X : TopCat.{w}) {n : ℕ} {x : X}
    (p : GenLoop (Fin (n + 1)) X x) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i (genLoopSingularSimplex X p) =
      singularConstantSimplex X n x := by
  refine (X.toSSetObjEquiv _).injective (ContinuousMap.ext (fun z => ?_))
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [genLoopSingularSimplex, singularConstantSimplex, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  apply GenLoop.boundary p
  apply (Classical.choose_spec (exists_stdSimplex_cube_pair_homeomorph (n + 1)) _).mp
  refine ⟨i, ?_⟩
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (z : Fin (n + 1) → ℝ) i = 0
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_ne]


theorem genLoopSingularSimplex_const (X : TopCat.{w}) (n : ℕ) (x : X) :
    genLoopSingularSimplex X (GenLoop.const : GenLoop (Fin n) X x) =
      singularConstantSimplex X n x := by
  exact (X.toSSetObjEquiv _).injective (ContinuousMap.ext (fun _ => rfl))


theorem genLoopSingularSimplex_map {X Y : TopCat.{w}} (f : X ⟶ Y)
    {n : ℕ} {x : X} (p : GenLoop (Fin n) X x) :
    (TopCat.toSSet.map f).app _ (genLoopSingularSimplex X p) =
      genLoopSingularSimplex Y (mapGenLoop f.hom rfl p) := by
  exact (Y.toSSetObjEquiv _).injective (ContinuousMap.ext (fun _ => rfl))

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]


noncomputable def genLoopSingularHomologyClass (R : C) (X : TopCat.{w})
    {n : ℕ} {x : X} (p : GenLoop (Fin (n + 1)) X x) :
    R ⟶ (TopCat.toSSet.obj X).homology R (n + 1) :=
  singularSimplexHomologyClass R X (genLoopSingularSimplex X p) x
    (genLoopSingularSimplex_face X p)


theorem genLoopSingularHomologyClass_eq_of_homotopic (R : C) (X : TopCat.{w})
    {n : ℕ} {x : X} {p q : GenLoop (Fin (n + 1)) X x}
    (H : GenLoop.Homotopic p q) :
    genLoopSingularHomologyClass R X p = genLoopSingularHomologyClass R X q := by
  obtain ⟨H⟩ := H
  let e := Classical.choose (exists_stdSimplex_cube_pair_homeomorph (n + 1))
  let eC : C(stdSimplex ℝ (Fin (n + 2)), I^(Fin (n + 1))) := ⟨e, e.continuous⟩
  have hp : p.val.comp eC =
      X.toSSetObjEquiv _ (genLoopSingularSimplex X p) := by
    simp only [genLoopSingularSimplex, Equiv.apply_symm_apply, eC, e]
  have hq : q.val.comp eC =
      X.toSSetObjEquiv _ (genLoopSingularSimplex X q) := by
    simp only [genLoopSingularSimplex, Equiv.apply_symm_apply, eC, e]
  apply singularSimplexHomologyClass_eq_of_simplex_homotopy R X _ _ x
    (genLoopSingularSimplex_face X p) (genLoopSingularSimplex_face X q)
    ((H.toHomotopy.compContinuousMap eC).cast hp hq)
  intro i time z
  have hb : e (stdSimplex.map i.succAbove z) ∈ Cube.boundary (Fin (n + 1)) := by
    apply (Classical.choose_spec (exists_stdSimplex_cube_pair_homeomorph (n + 1)) _).mp
    refine ⟨i, ?_⟩
    change FunOnFinite.linearMap ℝ ℝ i.succAbove (z : Fin (n + 1) → ℝ) i = 0
    simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_ne]
  change H (time, e (stdSimplex.map i.succAbove z)) = x
  exact (H.eq_fst time hb).trans (GenLoop.boundary p _ hb)


noncomputable def homotopyGroupSingularHomologyMap (R : C) (X : TopCat.{w})
    (n : ℕ) (x : X) :
    HomotopyGroup.Pi (n + 1) X x →
      (R ⟶ (TopCat.toSSet.obj X).homology R (n + 1)) :=
  Quotient.lift (genLoopSingularHomologyClass R X)
    (fun _ _ h => genLoopSingularHomologyClass_eq_of_homotopic R X h)


theorem homotopyGroupSingularHomologyMap_mk (R : C) (X : TopCat.{w})
    {n : ℕ} {x : X} (p : GenLoop (Fin (n + 1)) X x) :
    homotopyGroupSingularHomologyMap R X n x ⟦p⟧ =
      genLoopSingularHomologyClass R X p := rfl


theorem homotopyGroupSingularHomologyMap_one (R : C) (X : TopCat.{w})
    (n : ℕ) (x : X) :
    homotopyGroupSingularHomologyMap R X n x 1 = 0 := by
  rw [HomotopyGroup.one_def, homotopyGroupSingularHomologyMap_mk]
  exact (show singularSimplexHomologyClass R X (genLoopSingularSimplex X GenLoop.const) x
    (genLoopSingularSimplex_face X GenLoop.const) = 0 by
      simp only [genLoopSingularSimplex_const, singularSimplexHomologyClass_const])


theorem homotopyGroupSingularHomologyMap_naturality (R : C)
    {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) (x : X)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    homotopyGroupSingularHomologyMap R X n x a ≫
      SSet.homologyMap (TopCat.toSSet.map f) R (n + 1) =
        homotopyGroupSingularHomologyMap R Y n (f x)
          (homotopyGroupMap (Fin (n + 1)) f.hom rfl a) := by
  refine Quotient.inductionOn a (fun p => ?_)
  simp only [homotopyGroupMap_mk, homotopyGroupSingularHomologyMap_mk]
  unfold genLoopSingularHomologyClass
  simpa only [genLoopSingularSimplex_map] using
    singularSimplexHomologyClass_naturality R f (genLoopSingularSimplex X p) x
      (genLoopSingularSimplex_face X p)

end Poincare.Topology
