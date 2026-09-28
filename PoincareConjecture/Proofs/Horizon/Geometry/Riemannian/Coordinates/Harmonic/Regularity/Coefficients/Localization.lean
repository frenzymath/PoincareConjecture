import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Flux
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Potential.Stationary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Regularity









noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}



theorem coordinateErrorFlux_eq_of_eqOn
    {E F : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hsupp : tsupport u ⊆ U) (hEF : EqOn E F U) (i : Fin n) :
    coordinateErrorFlux E u i = coordinateErrorFlux F u i := by
  funext x
  by_cases hx : x ∈ U
  · simp only [coordinateErrorFlux, hEF hx]
  · have hxu : x ∉ tsupport u := fun h => hx (hsupp h)
    have hdu : fderiv ℝ u x = 0 := fderiv_of_notMem_tsupport ℝ hxu
    simp [coordinateErrorFlux, gradient, hdu]

end PoincareConjecture.HarmonicCoordinates

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem stationaryEllipticResidual_coordinateErrorFlux_eq_density_mul_laplacian
    (D : LeviCivitaData g) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {E : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : ContDiff ℝ ∞ u)
    (hsupp : tsupport u ⊆ U)
    (hE : EqOn E (fun x => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
      g.euclideanDivergenceOperator x) U) (x : EuclideanSpace ℝ (Fin n)) :
    Poincare.Parabolic.Interior.stationaryEllipticResidual u
      (HarmonicCoordinates.coordinateErrorFlux E u) (EuclideanSpace.basisFun (Fin n) ℝ) x =
      g.pullbackVolumeDensity id x * D.laplacian u x := by
  have hflux (i : Fin n) := HarmonicCoordinates.coordinateErrorFlux_eq_of_eqOn hsupp hE i
  unfold Poincare.Parabolic.Interior.stationaryEllipticResidual
  simp_rw [hflux]
  change Poincare.Parabolic.Interior.Kernel.lapEval (fderiv ℝ (fderiv ℝ u) x) -
    (∑ i, fderiv ℝ (fun y =>
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
        g.euclideanDivergenceOperator y) (_root_.gradient u y)) i) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)) = _
  rw [D.lapEval_fderiv_eq_metric_add_divergence hu]
  ring


theorem stationaryEllipticResidual_coordinateErrorFlux_eq_zero_of_notMem_tsupport
    (D : LeviCivitaData g) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {E : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : ContDiff ℝ ∞ u)
    (hsupp : tsupport u ⊆ U)
    (hE : EqOn E (fun x => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
      g.euclideanDivergenceOperator x) U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport u) :
    Poincare.Parabolic.Interior.stationaryEllipticResidual u
      (HarmonicCoordinates.coordinateErrorFlux E u) (EuclideanSpace.basisFun (Fin n) ℝ) x = 0 := by
  rw [D.stationaryEllipticResidual_coordinateErrorFlux_eq_density_mul_laplacian hu hsupp hE,
    D.laplacian_eq_zero_of_notMem_tsupport hx, mul_zero]



theorem norm_stationaryEllipticResidual_coordinateErrorFlux_le
    (D : LeviCivitaData g) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {E : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : ContDiff ℝ ∞ u)
    (hsupp : tsupport u ⊆ U)
    (hE : EqOn E (fun x => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) -
      g.euclideanDivergenceOperator x) U)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ tsupport u, |g.pullbackVolumeDensity id x * D.laplacian u x| ≤ B)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Poincare.Parabolic.Interior.stationaryEllipticResidual u
      (HarmonicCoordinates.coordinateErrorFlux E u) (EuclideanSpace.basisFun (Fin n) ℝ) x‖ ≤ B := by
  by_cases hx : x ∈ tsupport u
  · rw [D.stationaryEllipticResidual_coordinateErrorFlux_eq_density_mul_laplacian hu hsupp hE,
      Real.norm_eq_abs]
    exact hB x hx
  · rw [D.stationaryEllipticResidual_coordinateErrorFlux_eq_zero_of_notMem_tsupport
      hu hsupp hE hx, norm_zero]
    exact hB0

end PoincareConjecture.LeviCivitaData
