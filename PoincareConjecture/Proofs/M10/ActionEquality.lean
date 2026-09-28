import PoincareConjecture.Proofs.M10.GramEquality
import PoincareConjecture.Proofs.M10.GaussianNormalization

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem exponentialSliceJacobian_eq_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n)
    (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) (hτb : τ < b) :
    exponentialSliceJacobian G τ x = (2 * Real.sqrt τ) ^ n := by
  have hmatrix : (fun i j : Fin n ↦
      pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      (4 * τ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    rw [exponential_pairing_eq_of_volume_eq hL hDifferential G hmax hT hwindow
      hcurvature hb hbmax heq x _ _ hτ hτb]
    change 4 * τ * inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) = (4 * τ) * (1 : Matrix (Fin n) (Fin n) ℝ) i j
    simp only [OrthonormalBasis.inner_eq_ite, Matrix.one_apply]
  change Real.sqrt (Matrix.det _) = _
  rw [hmatrix]
  exact sqrt_det_four_mul_identity n hτ.le

theorem normalized_action_eq_norm_sq_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax)
    (heq : reducedVolume F T p b = euclideanReducedVolume n)
    (x : EuclideanSpace ℝ (Fin n)) {τ : ℝ} (hτ : 0 < τ) (hτb : τ < b) :
    G.toLExponentialFamily.action (metricCoordinates (F.metric T) p x) τ /
      (2 * Real.sqrt τ) = ‖x‖ ^ 2 := by
  let a := G.toLExponentialFamily.action (metricCoordinates (F.metric T) p x) τ /
    (2 * Real.sqrt τ)
  have hw := congrFun (weightedExponentialJacobian_eq_gaussian_of_volume_eq hL
    hDifferential G hmax hT hwindow hcurvature hτ (hτb.trans hbmax)
    (reducedVolume_eq_euclidean_of_le hL hDifferential G hmax hT hwindow hcurvature
      hb hbmax hτ hτb.le heq)) x
  change Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-a) *
    exponentialSliceJacobian G τ x = (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2) at hw
  rw [exponentialSliceJacobian_eq_of_volume_eq hL hDifferential G hmax hT hwindow
    hcurvature hb hbmax heq x hτ hτb] at hw
  have he : (2 : ℝ) ^ n * Real.exp (-a) = (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2) := by
    calc
      _ = (Real.rpow τ (-(n : ℝ) / 2) * (2 * Real.sqrt τ) ^ n) * Real.exp (-a) := by
        rw [rpow_mul_gaussian_jacobian n hτ]
      _ = _ := by nlinarith only [hw]
  have h := Real.exp_injective (mul_left_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)) he)
  exact neg_injective h

end PoincareConjecture.M10
