import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CocyclePathIntegral
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.IncidenceSingularCycles
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex









set_option autoImplicit false

open CategoryTheory
open scoped Simplicial BigOperators

namespace PoincareConjecture.M76.CutGraph

private theorem interval_simplex_zero :
    stdSimplexHomeomorphUnitInterval.symm 0 = stdSimplex.vertex (S := ℝ) (0 : Fin 2) :=
  stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr stdSimplexHomeomorphUnitInterval_zero.symm

private theorem interval_simplex_one :
    stdSimplexHomeomorphUnitInterval.symm 1 = stdSimplex.vertex (S := ℝ) (1 : Fin 2) :=
  stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr stdSimplexHomeomorphUnitInterval_one.symm

noncomputable def simplexEdgePath {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin 2), X)) :
    Path (f (stdSimplex.vertex 0)) (f (stdSimplex.vertex 1)) where
  toFun t := f (stdSimplexHomeomorphUnitInterval.symm t)
  continuous_toFun := f.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
  source' := congrArg f interval_simplex_zero
  target' := congrArg f interval_simplex_one

end PoincareConjecture.M76.CutGraph

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

open PoincareConjecture.M76.CutGraph

variable {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

noncomputable def singularValue (c : A.ModTwoEdgeCocycle)
    (s : (TopCat.toSSet.obj (TopCat.of A.barycentricSpace)) _⦋1⦌) : ZMod 2 :=
  c.pathValue (simplexEdgePath ((TopCat.of A.barycentricSpace).toSSetObjEquiv _ s))

theorem singularValue_pathSimplex (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} (p : Path x y) :
    c.singularValue (pathSimplex (X := TopCat.of A.barycentricSpace) p) = c.pathValue p := by
  let L := c.isCoveringMap.liftPath p.toContinuousMap (c.sheetPoint x 0) p.source
  let LP : Path (c.sheetPoint x 0) (L 1) :=
    ⟨L, c.isCoveringMap.liftPath_zero p.toContinuousMap (c.sheetPoint x 0) p.source, rfl⟩
  let f := (TopCat.of A.barycentricSpace).toSSetObjEquiv _
    (pathSimplex (X := TopCat.of A.barycentricSpace) p)
  have hL (t) : c.bundle.proj (LP t) = simplexEdgePath f t := by
    change c.bundle.proj (L t) =
      p (stdSimplexHomeomorphUnitInterval (stdSimplexHomeomorphUnitInterval.symm t))
    rw [Homeomorph.apply_symm_apply]
    exact congr_fun (c.isCoveringMap.liftPath_lifts p.toContinuousMap
      (c.sheetPoint x 0) p.source) t
  have h := c.pathValue_of_lift (simplexEdgePath f) LP hL
  change c.pathValue (simplexEdgePath f) = c.pathValue p
  change c.pathValue (simplexEdgePath f) = c.pathValue p - 0 at h
  exact h.trans (sub_zero _)


theorem singularValue_cocycle (c : A.ModTwoEdgeCocycle)
    (s : (TopCat.toSSet.obj (TopCat.of A.barycentricSpace)) _⦋2⦌) :
    (∑ j : Fin 3, ((-1 : ℤ) ^ j.val) •
      c.singularValue ((TopCat.toSSet.obj (TopCat.of A.barycentricSpace)).δ j s)) = 0 := by
  let X := TopCat.of A.barycentricSpace
  let f : C(stdSimplex ℝ (Fin 3), A.barycentricSpace) := X.toSSetObjEquiv _ s
  let v : Fin 3 → stdSimplex ℝ (Fin 3) := stdSimplex.vertex
  let : ContractibleSpace (stdSimplex ℝ (Fin 3)) :=
    (convex_stdSimplex ℝ (Fin 3)).contractibleSpace ⟨v 0, (v 0).property⟩
  let : LocallyPathConnectedSpace (stdSimplex ℝ (Fin 3)) :=
    (convex_stdSimplex ℝ (Fin 3)).locallyPathConnectedSpace
  obtain ⟨F, ⟨_, hF⟩, _⟩ := c.isCoveringMap.existsUnique_continuousMap_lifts
    f (v 0) (c.sheetPoint (f (v 0)) 0) rfl
  let face (j : Fin 3) : C(stdSimplex ℝ (Fin 2), stdSimplex ℝ (Fin 3)) :=
    ⟨stdSimplex.map j.succAbove, stdSimplex.continuous_map j.succAbove⟩
  have hedge (j : Fin 3) : c.singularValue ((TopCat.toSSet.obj X).δ j s) =
      c.sheetCoordinate (F (v (j.succAbove 1))) -
        c.sheetCoordinate (F (v (j.succAbove 0))) := by
    have hf : X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ j s) = f.comp (face j) := by
      ext z
      rw [TopCat.toSSetObjEquiv_δ_apply]
      rfl
    change c.pathValue (simplexEdgePath (X.toSSetObjEquiv (Opposite.op ⦋1⦌)
      ((TopCat.toSSet.obj X).δ j s))) = _
    rw [hf]
    have hlift (t : unitInterval) :
        c.bundle.proj (simplexEdgePath (F.comp (face j)) t) =
          simplexEdgePath (f.comp (face j)) t :=
      congr_fun hF (face j (stdSimplexHomeomorphUnitInterval.symm t))
    have h := c.pathValue_of_lift (simplexEdgePath (f.comp (face j)))
      (simplexEdgePath (F.comp (face j))) hlift
    simpa only [ContinuousMap.comp_apply, face, ContinuousMap.coe_mk,
      stdSimplex.map_vertex] using h
  change (∑ j : Fin 3, ((-1 : ℤ) ^ j.val) •
    c.singularValue ((TopCat.toSSet.obj X).δ j s)) = 0
  simp only [hedge, Fin.sum_univ_succ]
  norm_num [Fin.succAbove, show (1 : Fin 3) < 2 by decide,
    show (0 : Fin 3) < 2 by decide]

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
