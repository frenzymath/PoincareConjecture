import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.FiniteNerveChains
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.OrderComplexStars
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj










set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]



theorem orderComplex_simplex_mem {n : ℕ} (s : (nerve J) _⦋n⦌)
    (t : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplex.map s.obj t).val ∈ (finiteOrderComplex J).space := by
  classical
  have hrange (j : J) (hj : (stdSimplex.map s.obj t).val j ≠ 0) :
      ∃ i, s.obj i = j := by
    by_contra! h
    apply hj
    change FunOnFinite.linearMap ℝ ℝ s.obj t.val j = 0
    simp only [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro i hi
    exact ((h i) (Finset.mem_filter.mp hi).2).elim
  apply (finiteOrderComplex_space J _).mpr
  refine ⟨(stdSimplex.map s.obj t).property.1,
    (stdSimplex.map s.obj t).property.2, ?_⟩
  intro i j hi hj
  obtain ⟨a, rfl⟩ := hrange i hi
  obtain ⟨b, rfl⟩ := hrange j hj
  exact (le_total a b).imp (fun h => s.monotone h) (fun h => s.monotone h)



def orderComplexSimplex {n : ℕ} (s : (nerve J) _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n + 1)), (finiteOrderComplex J).space) where
  toFun t := ⟨(stdSimplex.map s.obj t).val, orderComplex_simplex_mem s t⟩
  continuous_toFun := (continuous_subtype_val.comp
    (stdSimplex.continuous_map s.obj)).subtype_mk _

open scoped Classical in


theorem orderComplexSimplex_vertex {n : ℕ} (s : (nerve J) _⦋n⦌)
    (i : Fin (n + 1)) :
    (orderComplexSimplex s (stdSimplex.vertex i)).val = Pi.single (s.obj i) 1 := by
  classical
  change (stdSimplex.map s.obj (stdSimplex.vertex i)).val = _
  rw [stdSimplex.map_vertex]




theorem orderComplexSimplex_comp {n m : SimplexCategory} (f : n ⟶ m)
    (s : (nerve J).obj (Opposite.op m)) :
    (orderComplexSimplex s).comp ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ =
      orderComplexSimplex ((nerve J).map f.op s) := by
  ext t : 1
  apply Subtype.ext
  change (stdSimplex.map s.obj (stdSimplex.map f t)).val = _
  rw [stdSimplex.map_comp_apply]
  rfl




def singularMapOfContinuousSimplices (A : SSet.{u}) (X : TopCat.{u})
    (F : ∀ n : SimplexCategory, A.obj (Opposite.op n) →
      C(stdSimplex ℝ (Fin (n.len + 1)), X))
    (hF : ∀ {n m : SimplexCategory} (f : n ⟶ m) (s : A.obj (Opposite.op m)),
      (F m s).comp ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ =
        F n (A.map f.op s)) : A ⟶ TopCat.toSSet.obj X where
  app n := ↾fun s => (X.toSSetObjEquiv n).symm (F n.unop s)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro s
    change (X.toSSetObjEquiv m).symm (F m.unop (A.map f s)) =
      (TopCat.toSSet.obj X).map f ((X.toSSetObjEquiv n).symm (F n.unop s))
    exact (congrArg (X.toSSetObjEquiv m).symm (hF f.unop s).symm).trans
      (TopCat.toSSetObjEquiv_symm_naturality f.unop (F n.unop s)).symm




def orderComplexSingular (J : Type u) [PartialOrder J] [Fintype J] :
    nerve J ⟶ TopCat.toSSet.obj (TopCat.of (finiteOrderComplex J).space) :=
  singularMapOfContinuousSimplices (nerve J) (TopCat.of (finiteOrderComplex J).space)
    (fun _ s => orderComplexSimplex s) (fun f s => orderComplexSimplex_comp f s)

end PoincareConjecture.Proofs.M59
