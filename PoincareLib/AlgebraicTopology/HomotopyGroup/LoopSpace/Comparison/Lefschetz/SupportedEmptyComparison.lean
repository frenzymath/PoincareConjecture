import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SupportedComparison
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology
import Mathlib.Algebra.Homology.QuasiIso

/-!
# The empty selected set in the characteristic comparison

The empty selected nerve has no simplices, and its coordinate
neighborhood has no points. Its actual characteristic map is therefore
already a simplicial isomorphism.
Source: the initial case of Hatcher, Theorem 2.27, pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]
  {E : Type u} [TopologicalSpace E] (p : C(E, (finiteOrderComplex J).space))

/-- The empty selected coordinate neighborhood contains no points.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem liftedCoordinateNeighborhood_empty_isEmpty :
    IsEmpty (liftedCoordinateNeighborhood p (∅ : Finset J)) := by
  refine ⟨fun x => ?_⟩
  have h := (mem_orderComplexNeighborhood_iff (∅ : Finset J) (p x.val)).mp x.property
  obtain ⟨i, hi, _⟩ := h
  exact Finset.notMem_empty i hi

/-- The actual characteristic map for the empty selected set is
degreewise a bijection between empty types. Source: Hatcher, Theorem 2.27. -/
theorem supportedSingularComparison_empty_isIso :
    IsIso (supportedSingularComparison p (∅ : Finset J)) := by
  let := liftedCoordinateNeighborhood_empty_isEmpty p
  have (n : SimplexCategoryᵒᵖ) :
      IsIso ((supportedSingularComparison p (∅ : Finset J)).app n) := by
    apply (isIso_iff_bijective _).mpr
    constructor
    · intro a _ _
      exact (Finset.notMem_empty _ (a.property 0)).elim
    · intro y
      exact isEmptyElim
        ((TopCat.of (liftedCoordinateNeighborhood p (∅ : Finset J))).toSSetObjEquiv n y
          (stdSimplex.vertex 0))
  exact NatIso.isIso_of_isIso_app _

/-- The empty selected-set comparison is an actual chain
quasi-isomorphism. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem supportedSingularComparison_empty_quasiIso :
    QuasiIso (SSet.chainComplexMap (supportedSingularComparison p (∅ : Finset J))
      integralCoefficient.{u}) := by
  let := supportedSingularComparison_empty_isIso p
  infer_instance

end PoincareMT.Proofs.M59
