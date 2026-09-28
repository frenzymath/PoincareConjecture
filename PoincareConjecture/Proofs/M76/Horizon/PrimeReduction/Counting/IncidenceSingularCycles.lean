import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.IncidenceCycleRank
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Subdivision.SingularCycles
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits









set_option autoImplicit false

open CategoryTheory Limits
open scoped BigOperators Simplicial

universe u v

namespace PoincareConjecture.M76.CutGraph

variable {K : Type v} [Field K] {V I : Type*} [Fintype V] [Fintype I]
  [DecidableEq V] [DecidableEq I]

noncomputable def pathSimplex {X : TopCat.{u}} {a b : X} (p : Path a b) :
    (TopCat.toSSet.obj X) _⦋1⦌ :=
  (X.toSSetObjEquiv _).symm
    (p.toContinuousMap.comp ⟨stdSimplexHomeomorphUnitInterval,
      stdSimplexHomeomorphUnitInterval.continuous⟩)

theorem pathSimplex_face_zero {X : TopCat.{u}} {a b : X} (p : Path a b) :
    (TopCat.toSSet.obj X).δ 0 (pathSimplex p) =
      Poincare.Topology.singularConstantSimplex X 0 b := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change p (stdSimplexHomeomorphUnitInterval
    (stdSimplex.map (0 : Fin 2).succAbove z)) = b
  have hz : stdSimplexHomeomorphUnitInterval
      (stdSimplex.map (0 : Fin 2).succAbove z) = 1 := by
    apply Subtype.ext
    norm_num [stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
      stdSimplex.map, FunOnFinite.linearMap_apply_apply, Finset.filter_singleton]
  rw [hz, p.target]

theorem pathSimplex_face_one {X : TopCat.{u}} {a b : X} (p : Path a b) :
    (TopCat.toSSet.obj X).δ 1 (pathSimplex p) =
      Poincare.Topology.singularConstantSimplex X 0 a := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change p (stdSimplexHomeomorphUnitInterval
    (stdSimplex.map (1 : Fin 2).succAbove z)) = a
  have hz : stdSimplexHomeomorphUnitInterval
      (stdSimplex.map (1 : Fin 2).succAbove z) = 0 := by
    apply Subtype.ext
    simp [stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
      stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  rw [hz, p.source]

variable (A : ModuleCat.{u} K) (X : TopCat.{u})

noncomputable def singularVertexChain (a : V → X) :
    (V → K) →ₗ[K] (A ⟶ ((TopCat.toSSet.obj X).chainComplex A).X 0) :=
  ∑ v, (LinearMap.proj v).smulRight ((TopCat.toSSet.obj X).ιChainComplex
    (Poincare.Topology.singularConstantSimplex X 0 (a v)))

noncomputable def singularEdgeChain (ends : I → Bool → V) (a : V → X)
    (p : ∀ i, Path (a (ends i false)) (a (ends i true))) :
    (I → K) →ₗ[K] (A ⟶ ((TopCat.toSSet.obj X).chainComplex A).X 1) :=
  ∑ i, (LinearMap.proj i).smulRight ((TopCat.toSSet.obj X).ιChainComplex
    (pathSimplex (p i)))

theorem singularVertexChain_single (a : V → X) (v : V) :
    singularVertexChain A X a (Pi.single v 1) =
      (TopCat.toSSet.obj X).ιChainComplex
        (Poincare.Topology.singularConstantSimplex X 0 (a v)) := by
  simp [singularVertexChain, LinearMap.sum_apply, Pi.single_apply]

omit [DecidableEq I] in
theorem singularEdgeChain_boundary (ends : I → Bool → V) (a : V → X)
    (p : ∀ i, Path (a (ends i false)) (a (ends i true))) (c : I → K) :
    singularEdgeChain A X ends a p c ≫ ((TopCat.toSSet.obj X).chainComplex A).d 1 0 =
      singularVertexChain A X a (incidenceBoundary ends c) := by
  simp only [singularEdgeChain, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, Preadditive.sum_comp, Linear.smul_comp,
    SSet.ιChainComplex_d, incidenceBoundary_apply, map_sum, map_smul, map_sub,
    singularVertexChain_single]
  simp [Fin.sum_univ_succ, pathSimplex_face_zero, pathSimplex_face_one, sub_eq_add_neg]

omit [DecidableEq I] in
theorem singularEdgeChain_cycle (ends : I → Bool → V) (a : V → X)
    (p : ∀ i, Path (a (ends i false)) (a (ends i true)))
    (c : LinearMap.ker (incidenceBoundary (K := K) ends)) :
    singularEdgeChain A X ends a p c ≫ ((TopCat.toSSet.obj X).chainComplex A).d 1 0 = 0 := by
  rw [singularEdgeChain_boundary, c.property, map_zero]


noncomputable def singularCycleLift (ends : I → Bool → V) (a : V → X)
    (p : ∀ i, Path (a (ends i false)) (a (ends i true))) :
    LinearMap.ker (incidenceBoundary (K := K) ends) →ₗ[K]
      (A ⟶ ((TopCat.toSSet.obj X).chainComplex A).cycles 1) where
  toFun c := ((TopCat.toSSet.obj X).chainComplex A).liftCycles
    (singularEdgeChain A X ends a p c) 0 (by simp)
    (singularEdgeChain_cycle A X ends a p c)
  map_add' c d := by
    apply (cancel_mono (((TopCat.toSSet.obj X).chainComplex A).iCycles 1)).mp
    simp only [Preadditive.add_comp, HomologicalComplex.liftCycles_i,
      Submodule.coe_add, map_add]
  map_smul' r c := by
    apply (cancel_mono (((TopCat.toSSet.obj X).chainComplex A).iCycles 1)).mp
    simp only [Linear.smul_comp, HomologicalComplex.liftCycles_i,
      Submodule.coe_smul, map_smul, RingHom.id_apply]



noncomputable def singularCycleClass (ends : I → Bool → V) (a : V → X)
    (p : ∀ i, Path (a (ends i false)) (a (ends i true))) :
    LinearMap.ker (incidenceBoundary (K := K) ends) →ₗ[K]
      (A ⟶ (TopCat.toSSet.obj X).homology A 1) where
  toFun c := singularCycleLift A X ends a p c ≫
    ((TopCat.toSSet.obj X).chainComplex A).homologyπ 1
  map_add' c d := by simp only [map_add, Preadditive.add_comp]
  map_smul' r c := by simp only [map_smul, Linear.smul_comp, RingHom.id_apply]

end PoincareConjecture.M76.CutGraph
