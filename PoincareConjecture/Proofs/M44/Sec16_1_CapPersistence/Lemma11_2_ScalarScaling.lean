import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.M01.NormalizationMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Scaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M44

section Homothety

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N]

theorem homothety_ricciNormSq_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) : D'.ricciNormSq (f x) = D.ricciNormSq x / Q ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    infer_instance
  let b := g.orthonormalBasis x
  let e := M13.homothetyTangentIsometry g h f Q hQ hf x
  have heval (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D'.ricci (f x) (e (b i)) (e (b j)) = D.ricci x (b i) (b j) / Q := by
    change M13.ricciLinear D' (f x)
      ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x (b i))
      ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x (b j)) = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, M13.ricciLinear_apply]
    rw [M13.homothety_ricci_eq g h f Q hQ hf D D', ← mul_assoc,
      M13.inv_sqrt_mul_inv_sqrt Q hQ.le, div_eq_mul_inv, mul_comm]
  have hn := M13.sum_sq_bilinear_basis_eq (M13.ricciLinear D' (f x))
    (h.orthonormalBasis (f x)) (b.map e)
  have hn0 := M13.sum_sq_bilinear_basis_eq (M13.ricciLinear D x)
    (g.orthonormalBasis x) b
  change D'.ricciNormSq (f x) = ∑ i, ∑ j, D'.ricci (f x) (e (b i)) (e (b j)) ^ 2 at hn
  change D.ricciNormSq x = ∑ i, ∑ j, D.ricci x (b i) (b j) ^ 2 at hn0
  simpa only [heval, div_pow, ← Finset.sum_div, ← hn0] using hn

end Homothety

section Scaling

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

theorem rescaled_gradient (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    (f : M → ℝ) (x : M) :
    (m01RescaledMetric_connection g D Q hQ).gradient f x = Q⁻¹ • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  have h := (m01RescaledMetric_connection g D Q hQ).inner_gradient f x v
  change Q * g.inner x ((m01RescaledMetric_connection g D Q hQ).gradient f x) v =
    mvfderiv (𝓡 n) f x v at h
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]
  apply (mul_left_cancel₀ hQ.ne')
  rw [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]
  exact h

theorem rescaled_laplacian (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) :
    (m01RescaledMetric_connection g D Q hQ).laplacian f x = Q⁻¹ * D.laplacian f x := by
  have hgrad : (m01RescaledMetric_connection g D Q hQ).gradient f =
      Q⁻¹ • D.gradient f := funext fun y => rescaled_gradient D hQ f y
  rw [(m01RescaledMetric_connection g D Q hQ).laplacian_eq_trace_connection_gradient hf,
    D.laplacian_eq_trace_connection_gradient hf, hgrad]
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
    (D.connection (Q⁻¹ • D.gradient f) x).toLinearMap = _
  rw [D.connection.isCovariantDerivativeOnUniv.smul_const Q⁻¹
    ((D.contMDiffAt_gradient hf).mdifferentiableAt (by simp))]
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
    (Q⁻¹ • (D.connection (D.gradient f) x).toLinearMap) = _
  exact (LinearMap.trace ℝ (TangentSpace (𝓡 n) x)).map_smul Q⁻¹ _

theorem rescaledMetric_identity_homothety {Q : ℝ} (hQ : 0 < Q) :
    MetricHomothety g (m01RescaledMetric g Q hQ) (Diffeomorph.refl (𝓡 n) M ∞) Q := by
  intro x v w
  simp only [Diffeomorph.coe_refl, mfderiv_id]
  exact m01RescaledMetric_inner g Q hQ x v w

theorem rescaled_scalar_evolution [T2Space M] (D : LeviCivitaData g)
    {Q : ℝ} (hQ : 0 < Q) (x : M)
    (hscalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature) :
    let DQ := m01RescaledMetric_connection g D Q hQ
    DQ.laplacian DQ.scalarCurvature x + 2 * DQ.ricciNormSq x =
      (D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) / Q ^ 2 := by
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hS : DQ.scalarCurvature = fun y => Q⁻¹ * D.scalarCurvature y := by
    funext y
    have h := M13.homothety_scalarCurvature_eq g (m01RescaledMetric g Q hQ)
      (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (rescaledMetric_identity_homothety hQ) D DQ y
    simpa only [Diffeomorph.coe_refl, id_eq, div_eq_mul_inv, mul_comm] using h
  have hR : DQ.ricciNormSq x = D.ricciNormSq x / Q ^ 2 := by
    exact homothety_ricciNormSq_eq g (m01RescaledMetric g Q hQ)
      (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (rescaledMetric_identity_homothety hQ) D DQ x
  change DQ.laplacian DQ.scalarCurvature x + 2 * DQ.ricciNormSq x = _
  rw [hS, DQ.laplacian_const_mul, hR, rescaled_laplacian D hQ (hscalar x)]
  field_simp

end Scaling

end PoincareConjecture.M44
