import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.CurvatureBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Hessian.Divergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Cauchy








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


theorem hessianCurvatureFlux_energy_le (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {K G : ℝ} (hcurv : D.curvatureTensorNorm x ≤ K)
    (hgrad : g.tangentNorm x (D.gradient f x) ≤ G) :
    g.tensorPairingThree (D.hessianCurvatureFlux f) (D.hessianCurvatureFlux f) x ≤
      (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * K ^ 2 * G ^ 2 := by
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans hcurv
  have hG : 0 ≤ G := (Real.sqrt_nonneg _).trans hgrad
  have h := D.sum_sq_hessian_curvature_flux_le f x
  have hraw : g.tensorPairingThree (D.hessianCurvatureFlux f) (D.hessianCurvatureFlux f) x ≤
      (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * D.curvatureTensorNorm x ^ 2 *
        g.tangentNorm x (D.gradient f x) ^ 2 := by
    simpa [RiemannianMetric.tensorPairingThree, hessianCurvatureFlux, pow_two] using h
  calc
    _ ≤ (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * D.curvatureTensorNorm x ^ 2 *
        g.tangentNorm x (D.gradient f x) ^ 2 := hraw
    _ ≤ _ := by gcongr <;> exact Real.sqrt_nonneg _


theorem twoTensorCurvatureTrace_pairing_lower (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin n)) {K : ℝ}
    (hcurv : D.curvatureTensorNorm x ≤ K) :
    -(2 * (n : ℝ) ^ 2 * K) * g.tensorPairingTwo T T x ≤
      g.tensorPairingTwo (D.twoTensorCurvatureTrace T) T x := by
  let A := D.twoTensorCurvatureTrace T
  let Q := g.tensorPairingTwo T T x
  let κ := 2 * (n : ℝ) ^ 2 * K
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans hcurv
  have hN : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hQ : 0 ≤ Q := g.tensorPairingTwo_self_nonneg T x
  have hA : g.tensorPairingTwo A A x ≤ κ ^ 2 * Q := by
    have h := D.sum_sq_two_tensor_curvature_trace_le hT x
    have heq : g.tensorPairingTwo A A x =
        ∑ i, ∑ j, (-(∑ k,
          (T x ![D.curvature x (g.orthonormalBasis x k) (g.orthonormalBasis x i)
            (g.orthonormalBasis x k), g.orthonormalBasis x j] +
          T x ![g.orthonormalBasis x k, D.curvature x (g.orthonormalBasis x k)
            (g.orthonormalBasis x i) (g.orthonormalBasis x j)]))) ^ 2 := by
      simp only [A, twoTensorCurvatureTrace, RiemannianMetric.tensorPairingTwo,
        Matrix.cons_val_zero, Matrix.cons_val_one, pow_two]
    rw [heq]
    calc
      _ ≤ 4 * (n : ℝ) ^ 4 * D.curvatureTensorNorm x ^ 2 * g.tensorNorm T x ^ 2 := h
      _ ≤ 4 * (n : ℝ) ^ 4 * K ^ 2 * g.tensorNorm T x ^ 2 := by
        gcongr
      _ = _ := by
        dsimp only [κ, Q]
        rw [g.tensorPairingTwo_self_eq_tensorNorm_sq]
        ring
  have hsqrt : Real.sqrt (g.tensorPairingTwo A A x) ≤ κ * Real.sqrt Q := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg hκ (Real.sqrt_nonneg _), ?_⟩
    rw [mul_pow, Real.sq_sqrt hQ]
    exact hA
  have habs := (g.abs_tensorPairingTwo_le A T x).trans
    (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg Q))
  have hmul : (κ * Real.sqrt Q) * Real.sqrt Q = κ * Q := by
    rw [mul_assoc, Real.mul_self_sqrt hQ]
  rw [hmul] at habs
  simpa only [A, κ, Q, neg_mul] using (abs_le.mp habs).1


theorem twoTensorCurvatureTrace_regularized_lower (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n (EuclideanSpace ℝ (Fin n)) 2}
    (hT : IsSmoothCovariantTensor T) (x : EuclideanSpace ℝ (Fin n)) {K ε : ℝ}
    (hcurv : D.curvatureTensorNorm x ≤ K) (hε : 0 ≤ ε) :
    -(2 * (n : ℝ) ^ 2 * K) * (g.tensorPairingTwo T T x + ε) ≤
      g.tensorPairingTwo (D.twoTensorCurvatureTrace T) T x := by
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans hcurv
  have h := D.twoTensorCurvatureTrace_pairing_lower hT x hcurv
  nlinarith only [h, mul_nonneg (show 0 ≤ 2 * (n : ℝ) ^ 2 * K by positivity) hε]



theorem hessianCurvatureFlux_regularized_energy_le (D : LeviCivitaData g)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {K G ε L : ℝ} (hL : 0 ≤ L)
    (hcurv : D.curvatureTensorNorm x ≤ K)
    (hgrad : g.tangentNorm x (D.gradient f x) ≤ G)
    (hscale : (n : ℝ) ^ 3 * ((n : ℝ) + 1) ^ 2 * K ^ 2 * G ^ 2 ≤ L * ε) :
    let T := fun y v => D.hessian f y (v 0) (v 1)
    g.tensorPairingThree (D.hessianCurvatureFlux f) (D.hessianCurvatureFlux f) x ≤
      L * (g.tensorPairingTwo T T x + ε) := by
  refine (D.hessianCurvatureFlux_energy_le f x hcurv hgrad).trans (hscale.trans ?_)
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (g.tensorPairingTwo_self_nonneg _ x)) hL

end PoincareConjecture.LeviCivitaData
