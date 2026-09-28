import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.DimensionInduction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.ThreeDimensional
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.AreaEstimates
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Hypersurface
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.LevelCutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularLevelScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.RegularLevels
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.MeanCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.LevelScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SlabError
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Annulus
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.LimitSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.AreaSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.PointedScalarAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Fiber
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Projection
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.RestrictedGradient
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiber
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Semiconcavity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Patching
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.CompactDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.RegularSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.Ascent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.AscentStability
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.Semiconcavity.Approximation
import PoincareConjecture.Proofs.Horizon.Analysis.InnerProductSpace.AlmostOpposite
import PoincareConjecture.Proofs.Horizon.Analysis.Approximation.Convolution.Directional
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Applications.Counterexamples
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Blowup
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.LimitPacking
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.LimitSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.AreaSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RegularRadius
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.PuncturedCover
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Spire
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.SpireRescaling
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.VariableRescaling
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Counterexamples
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.HypersurfaceSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

theorem exists_uniform_unitBall_scalar_integral_bound_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
        [IsManifold (𝓡 0) ∞ M]
        (g : RiemannianMetric 0 M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ (x : M) (v w : TangentSpace (𝓡 0) x),
          -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M,
          (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  refine ⟨1, by norm_num, ?_⟩
  intro M _ _ _ _ _ _ g D _ _ p
  have hscalar : ∀ x : M, D.scalarCurvature x = 0 := by
    intro x
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 0) x) = 0 := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0
      simp
    have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace (𝓡 0) x))) = 0 := by
      rw [Fintype.card_fin, hdim]
    letI : IsEmpty (Fin (Module.finrank ℝ (TangentSpace (𝓡 0) x))) :=
      Fintype.card_eq_zero_iff.mp hcard
    unfold LeviCivitaData.scalarCurvature
    exact Fintype.sum_empty _
  simp only [hscalar, integral_zero]
  norm_num

theorem exists_uniform_unitBall_scalar_integral_bound_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
        [IsManifold (𝓡 1) ∞ M]
        (g : RiemannianMetric 1 M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ (x : M) (v w : TangentSpace (𝓡 1) x),
          -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M,
          (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  refine ⟨1, by norm_num, ?_⟩
  intro M _ _ _ _ _ _ g D _ _ p
  have hscalar : ∀ x : M, D.scalarCurvature x = 0 := by
    intro x
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 1) x) = 1 := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1
      simp
    have hidx (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 1) x))) : i.val = 0 := by
      have hi : i.val < 1 := by simpa [hdim] using i.isLt
      omega
    unfold LeviCivitaData.scalarCurvature
    simp only [LeviCivitaData.ricci]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hij : i = j := Fin.ext (by simp [hidx i, hidx j])
    simpa [hij] using D.curvatureTensor_zero_first x (g.orthonormalBasis x i)
      (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  simp only [hscalar, integral_zero]
  norm_num

theorem exists_uniform_unitBall_scalar_integral_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ (x : M) (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M, (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  cases n with
  | zero =>
      simpa using exists_uniform_unitBall_scalar_integral_bound_zero
  | succ n =>
      cases n with
      | zero =>
          simpa using exists_uniform_unitBall_scalar_integral_bound_one
      | succ n =>
          cases n with
          | zero => exact exists_uniform_unitBall_scalar_integral_bound_two
          | succ n =>
              cases n with
              | zero => exact exists_uniform_unitBall_scalar_integral_bound_three
              | succ n =>
                  exact exists_uniform_unitBall_scalar_integral_bound_of_three_le _ (by omega)

end PoincareConjecture
