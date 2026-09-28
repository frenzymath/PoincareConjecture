import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SupportedComparison
import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyEquiv
import Mathlib.Algebra.Homology.QuasiIso










set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]
  {E : Type u} [TopologicalSpace E] (p : C(E, (finiteOrderComplex J).space))



theorem liftedCoordinateNeighborhood_empty_isEmpty :
    IsEmpty (liftedCoordinateNeighborhood p (∅ : Finset J)) := by
  refine ⟨fun x => ?_⟩
  have h := (mem_orderComplexNeighborhood_iff (∅ : Finset J) (p x.val)).mp x.property
  obtain ⟨i, hi, _⟩ := h
  exact Finset.notMem_empty i hi



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



theorem supportedSingularComparison_empty_quasiIso :
    QuasiIso (SSet.chainComplexMap (supportedSingularComparison p (∅ : Finset J))
      integralCoefficient.{u}) := by
  let := supportedSingularComparison_empty_isIso p
  infer_instance

end PoincareConjecture.Proofs.M59
