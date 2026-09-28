import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalShiHomothety
import PoincareConjecture.Proofs.M13.ConnectionScale
import PoincareConjecture.Proofs.M13.CurvatureTransport
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ManifoldCurvatureSmooth
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Linearity











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]

private theorem scale_riemannEvaluation_eq
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q)
    (x : M) (v : Fin 4 → TangentSpace (𝓡 n) x) :
    (M13.scaleLeviCivitaData D Q hQ).riemannEvaluation x v =
      Q * D.riemannEvaluation x v := by
  have h := M13.homothety_curvatureTensor_eq g (M13.scaleSmoothMetric g Q hQ)
    (Diffeomorph.refl (𝓡 n) M ∞) Q
    (M13.identity_metricHomothety g Q hQ) D
    (M13.scaleLeviCivitaData D Q hQ) x
    (v 0) (v 1) (v 2) (v 3)
  change (M13.scaleLeviCivitaData D Q hQ).curvatureTensor x
      (mfderiv (𝓡 n) (𝓡 n) id x (v 0))
      (mfderiv (𝓡 n) (𝓡 n) id x (v 1))
      (mfderiv (𝓡 n) (𝓡 n) id x (v 2))
      (mfderiv (𝓡 n) (𝓡 n) id x (v 3)) =
        Q * D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) at h
  simp only [mfderiv_id] at h
  change (M13.scaleLeviCivitaData D Q hQ).curvatureTensor x
      (v 0) (v 1) (v 2) (v 3) =
        Q * D.curvatureTensor x (v 0) (v 1) (v 2) (v 3) at h
  exact h

omit [T2Space M] in
private theorem tensorNorm_const_mul
    (g : RiemannianMetric n M) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (c : ℝ) (x : M) :
    g.tensorNorm (fun y v => c * T y v) x =
      |c| * g.tensorNorm T x := by
  unfold RiemannianMetric.tensorNorm
  calc
    Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (c * T x (fun i => g.orthonormalBasis x (a i))) ^ 2) =
      Real.sqrt (c ^ 2 * ∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (T x (fun i => g.orthonormalBasis x (a i))) ^ 2) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = Real.sqrt (c ^ 2) *
        Real.sqrt (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
          (T x (fun i => g.orthonormalBasis x (a i))) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg c)]
    _ = |c| * g.tensorNorm T x := by
          rw [Real.sqrt_sq_eq_abs]
          rfl

theorem scale_iterated_curvatureEvaluation_eq
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (m : ℕ) (x : M)
    (v : Fin (4 + m) → TangentSpace (𝓡 n) x) :
    (M13.scaleLeviCivitaData D Q hQ).iteratedCovariantTensorDerivative
        (M13.scaleLeviCivitaData D Q hQ).riemannEvaluation m x v =
      Q * D.iteratedCovariantTensorDerivative D.riemannEvaluation m x v := by
  induction m generalizing x with
  | zero =>
      simpa only [LeviCivitaData.iteratedCovariantTensorDerivative,
        Nat.add_zero] using scale_riemannEvaluation_eq g D Q hQ x v
  | succ m ih =>
      let DQ := M13.scaleLeviCivitaData D Q hQ
      have hsmooth : IsSmoothCovariantTensor
          (D.iteratedCovariantTensorDerivative D.riemannEvaluation m) :=
          D.iteratedCovariantTensorDerivative_isSmooth
            D.riemannEvaluation_isSmooth_manifold m
      have hlin := LeviCivitaData.covariantTensorDerivative_const_mul DQ
        hsmooth Q
      have hfun : DQ.iteratedCovariantTensorDerivative
          DQ.riemannEvaluation m =
          (fun y z => Q * D.iteratedCovariantTensorDerivative
            D.riemannEvaluation m y z) := by
        funext y z
        exact ih y z
      simp only [LeviCivitaData.iteratedCovariantTensorDerivative] at hlin ⊢
      rw [hfun]
      rw [hlin]
      rfl

theorem scale_curvatureDerivativeNorm_eq
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (m : ℕ) (x : M) :
    (M13.scaleLeviCivitaData D Q hQ).curvatureDerivativeNorm m x =
      Q * (Real.sqrt Q)⁻¹ ^ (4 + m) * D.curvatureDerivativeNorm m x := by
  let DQ := M13.scaleLeviCivitaData D Q hQ
  let S := D.iteratedCovariantTensorDerivative D.riemannEvaluation m
  have hraw : DQ.iteratedCovariantTensorDerivative DQ.riemannEvaluation m =
      (fun y v => Q * S y v) := by
    funext y v
    exact scale_iterated_curvatureEvaluation_eq g D Q hQ m y v
  have hS : IsSmoothCovariantTensor S :=
    D.iteratedCovariantTensorDerivative_isSmooth
      D.riemannEvaluation_isSmooth_manifold m
  obtain ⟨A, hA⟩ := hS.1 x
  have hnorm := tensorNorm_eq_of_homothety g (M13.scaleSmoothMetric g Q hQ)
    (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (M13.identity_metricHomothety g Q hQ)
    S S x (by
      intro v
      change S x v = S x (fun i =>
        mfderiv (𝓡 n) (𝓡 n) id x (v i))
      have hvid : (fun i => mfderiv (𝓡 n) (𝓡 n) id x (v i)) = v := by
        funext i
        simp only [mfderiv_id]
        rfl
      rw [hvid]) A hA
  have hfx : (Diffeomorph.refl (𝓡 n) M ∞) x = x := rfl
  rw [hfx] at hnorm
  change RiemannianMetric.tensorNorm (M13.scaleSmoothMetric g Q hQ)
      (DQ.iteratedCovariantTensorDerivative DQ.riemannEvaluation m) x = _
  rw [hraw, tensorNorm_const_mul, abs_of_pos hQ, hnorm]
  simp only [S, LeviCivitaData.curvatureDerivativeNorm]
  ring

end PoincareConjecture.M28
