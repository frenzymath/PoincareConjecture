import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Metric.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem rescaledMetric_curvatureTensor
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    (rescaledMetric_connection g D c hc).curvatureTensor x u v w z =
      c * D.curvatureTensor x u v w z := by
  unfold LeviCivitaData.curvatureTensor
  rw [rescaledMetric_inner]
  rfl

theorem rescaledMetric_bilinear_trace
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c) (x : M)
    (B : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ) :
    (∑ i, B ((rescaledMetric g c hc).orthonormalBasis x i)
      ((rescaledMetric g c hc).orthonormalBasis x i)) =
      c⁻¹ * ∑ i, B (g.orthonormalBasis x i) (g.orthonormalBasis x i) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := (g.orthonormalBasis x).toBasis
  have hgram : Matrix.of (fun i j =>
      (rescaledMetric g c hc).inner x (b i) (b j)) =
      Matrix.diagonal (fun _ : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) => c) := by
    ext i j
    change c * inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x j) = _
    rw [(g.orthonormalBasis x).inner_eq_ite]
    by_cases hij : i = j <;> simp [hij]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(rescaledMetric g c hc).toRiemannianMetric⟩
  have h := bilinear_sum_basis_eq_inverse_gram B b
    ((rescaledMetric g c hc).orthonormalBasis x)
  change (∑ i, B ((rescaledMetric g c hc).orthonormalBasis x i)
    ((rescaledMetric g c hc).orthonormalBasis x i)) =
      ∑ i, ∑ j, (Matrix.of (fun i j =>
        (rescaledMetric g c hc).inner x (b i) (b j)))⁻¹ i j * B (b i) (b j) at h
  have hinv : (Matrix.diagonal (fun _ : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) => c))⁻¹ =
      Matrix.diagonal (fun _ => c⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp [hc.ne']
  rw [h, hgram, hinv]
  simp [b, Matrix.diagonal_apply, Finset.mul_sum]

theorem rescaledMetric_ricci
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M) (u v : TangentSpace (𝓡 n) x) :
    (rescaledMetric_connection g D c hc).ricci x u v = D.ricci x u v := by
  let B : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun a b => D.curvatureTensor x u a v b)
      (fun a b d => D.curvatureTensor_add_second x u a b v d)
      (fun r a b => D.curvatureTensor_smul_second x r u a v b)
      (fun a b d => D.curvatureTensor_add_last x u a v b d)
      (fun r a b => D.curvatureTensor_smul_last x r u a v b)
  have h := rescaledMetric_bilinear_trace g c hc x B
  simp only [LeviCivitaData.ricci, rescaledMetric_curvatureTensor, ← Finset.mul_sum]
  change c * (∑ i, B ((rescaledMetric g c hc).orthonormalBasis x i)
    ((rescaledMetric g c hc).orthonormalBasis x i)) = _
  rw [h, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rfl

theorem rescaledMetric_scalarCurvature
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M) :
    (rescaledMetric_connection g D c hc).scalarCurvature x =
      c⁻¹ * D.scalarCurvature x := by
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have h := rescaledMetric_bilinear_trace g c hc x B
  simp only [LeviCivitaData.scalarCurvature]
  simp_rw [rescaledMetric_ricci]
  simpa only [B, LinearMap.sum_apply, LeviCivitaData.curvatureTensor_bilinear_first_third_apply,
    LeviCivitaData.ricci] using h

end PoincareConjecture
