import PoincareConjecture.Proofs.M47.TerminalCurvatureNativeBounds
import PoincareConjecture.Proofs.M36.CenteredNeckMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_exists_neck_native_realization
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (theta : UnitTwoSphere)
    (D0 : LeviCivitaData (M35.cylinderEuclideanMetric 0 (by norm_num))) :
    ∃ (g1 : RiemannianMetric 3 E) (_D1 : LeviCivitaData g1) (U : Set E),
      IsOpen U ∧ (0 : E) ∈ U ∧ U ⊆ centeredNeckDomain N 0 ∧
      (∀ x ∈ U, g1.euclideanCoefficients x =
        (normalizedNeckMetric N).pullbackCoefficients (centeredNeckLift N theta 0) x) ∧
      let H : CovariantTensorEvaluation 3 E 2 := fun y v =>
        g1.inner y (v 0) (v 1) - (M35.cylinderEuclideanMetric 0 (by norm_num)).inner y (v 0) (v 1)
      let g0 := M35.cylinderEuclideanMetric 0 (by norm_num)
      g0.tensorNorm H 0 ≤ N.epsilon ∧
        g0.tensorNorm (D0.covariantTensorDerivative H) 0 ≤ N.epsilon ∧
        g0.tensorNorm (D0.covariantTensorDerivative (D0.covariantTensorDerivative H)) 0 ≤
          N.epsilon := by
  have hs : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  obtain ⟨g1, D1, U, hU, h0, hdomain, hcoeff⟩ :=
    exists_centeredNeckMetric_realization N theta 0 (zero_mem_centeredNeckDomain N hs)
  have hnative (x : E) (hx : x ∈ U) (i j : Fin 3) :
      g1.inner x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient (fun z v w => normalizedNeckForm N z v w)
        (chartAt (EuclideanSpace ℝ (Fin 2)) theta) (M35.cylinderCoordinateEquiv x) i j := by
    have hh := congrArg (fun B => B (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j))
      ((hcoeff x hx).trans (normalizedNeckMetric_pullbackCoefficients N theta 0 (hdomain hx)))
    rw [centeredCylinderMetric, centeredCylinderBilinear_basis] at hh
    simp only [RiemannianMetric.euclideanCoefficients, cylinderEuclideanEquiv,
      show ((0 : EuclideanSpace ℝ (Fin 2)), (0 : ℝ)) = 0 from rfl, add_zero] at hh
    convert! hh using 1
  have hx : M35.cylinderCoordinateEquiv.symm ((0, 0) : RoundCylinderCoordinates) ∈ U := by
    simpa only [show ((0 : EuclideanSpace ℝ (Fin 2)), (0 : ℝ)) = 0 from rfl,
      map_zero] using h0
  have hbound := terminalCurvature_native_two_derivative_bounds N.epsilon_pos
    N.epsilon_lt_half.le (fun z v w => normalizedNeckForm N z v w) N.metric_comparison.close
    g1 D0 theta hU hnative 0 hs hx
  refine ⟨g1, D1, U, hU, h0, hdomain, hcoeff, ?_⟩
  simpa only [show ((0 : EuclideanSpace ℝ (Fin 2)), (0 : ℝ)) = 0 from rfl,
    map_zero] using hbound

end PoincareConjecture.M47
