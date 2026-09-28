import PoincareConjecture.Statements.Ch06.ReducedLength
import PoincareConjecture.Proofs.M08
import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M09.ExponentialFamily
import PoincareConjecture.Proofs.M09.GeometryAssembly
import PoincareConjecture.Proofs.M09.RegularLocusAssembly
import PoincareConjecture.Proofs.M09.RegularLaplacian
import PoincareConjecture.Proofs.M09.ZeroResidualBarrier
import PoincareConjecture.Proofs.M09.LocalBarrierBounds
import PoincareConjecture.Proofs.M09.RegularSharpEquality











set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]






















theorem reducedLengthDifferentialInequalities
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hM04 : RicciFlowCurvatureTheory.{u})
    (hL : LGeodesicTheory F T τmax) :
    Nonempty (ReducedLengthDifferentialTheory F T τmax) := by
  classical
  let A (p : M) : LExponentialFamily F T τmax p :=
    Classical.choice (Proofs.M09.nonempty_lExponentialFamily F hM04 T τmax
      hτmax hwindow hcurvature p)
  let G (p : M) : LExponentialGeometry F T τmax p :=
    Classical.choice (Proofs.M09.lExponentialFamily_exists_geometry F hM04 T τmax
      hτmax hwindow hcurvature hL p (A p))
  refine ⟨{
    regular_locus := fun p τ hτ hmax ↦
      Proofs.M09.lExponentialGeometry_regular_locus F hM04 T τmax hτmax hwindow
        hcurvature hL p (G p) τ hτ hmax
    regular_point_formulas := fun p _ _ r ↦
      Proofs.M09.regular_six_formulas hM04 hL hτmax hwindow (A p) r
    upper_barrier_extension := fun p q τ hτ hmax ε hε ↦
      Proofs.M09.exists_upperBarrier_with_residual_le hM04 hL hτmax hwindow
        (A p) q τ hτ hmax ε hε
    exponential_geometry := fun p ↦ ⟨G p⟩
    local_upper_barrier_bounds := fun p z hz ↦
      Proofs.M09.lExponentialFamily_local_upper_barrier_bounds F hM04 T τmax
        hτmax hwindow hcurvature hL p (A p) z hz
    regular_point_equality := ?_
  }⟩
  intro p H z hz
  exact Proofs.M09.regular_sharp_laplacian_tensor_eq hM04 hL hτmax hwindow
    H.toLExponentialFamily (H.regular_point z hz)


theorem reducedLengthDifferentialInequalities_from_M04_M08
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)) :
    Nonempty (ReducedLengthDifferentialTheory F T τmax) := by
  rcases lGeodesicExistenceAndVariation_from_M04 F T τmax hT hτmax hwindow hcurvature with ⟨hL⟩
  exact reducedLengthDifferentialInequalities F T τmax hT hτmax hwindow hcurvature
    ricciFlowCurvatureTheory hL

end PoincareConjecture
