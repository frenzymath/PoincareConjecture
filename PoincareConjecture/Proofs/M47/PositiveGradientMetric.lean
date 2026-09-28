import PoincareConjecture.Proofs.M47.PositiveGradientBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators NNReal

universe u

namespace PoincareConjecture.M47Positive

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem ricci_lower_of_unit_lower (D : LeviCivitaData g) (x : M) {c : ℝ}
    (hunit : ∀ v : TangentSpace (𝓡 n) x, g.inner x v v = 1 → c ≤ D.ricci x v v)
    (v : TangentSpace (𝓡 n) x) : c * g.inner x v v ≤ D.ricci x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x (b i) (b i)
  have hB (u w : TangentSpace (𝓡 n) x) : B u w = D.ricci x u w := by
    simp only [B, LinearMap.sum_apply,
      LeviCivitaData.curvatureTensor_bilinear_first_third_apply, LeviCivitaData.ricci, b]
  by_cases hv : v = 0
  · subst v
    rw [← hB]
    simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w := ‖v‖⁻¹ • v
  have hw : g.inner x w w = 1 := by
    change inner ℝ w w = 1
    rw [real_inner_self_eq_norm_sq]
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
    rw [inv_mul_cancel₀ hn.ne', one_pow]
  have h := hunit w hw
  rw [← hB] at h
  change c ≤ B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg ‖v‖)
  have hid : ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * B v v)) = B v v := by
    field_simp [hn.ne']
  rw [hid] at hmul
  rw [← hB]
  change c * inner ℝ v v ≤ B v v
  rw [real_inner_self_eq_norm_sq]
  nlinarith only [hmul]

theorem scalar_increment_le_of_gradient_energy_bound [T3Space M] [PreconnectedSpace M]
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {A : ℝ} (hA : 0 < A)
    (henergy : ∀ y, g.inner y (D.gradient f y) (D.gradient f y) ≤ A ^ 2)
    (p y : M) : |f p - f y| ≤ A * (g.edist p y).toReal := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let K : ℝ≥0 := ⟨A, hA.le⟩
  have hnorm (z : M) : g.tangentNorm z (D.gradient f z) ≤ A := by
    change Real.sqrt (g.inner z (D.gradient f z) (D.gradient f z)) ≤ A
    exact (Real.sqrt_le_left hA.le).mpr (henergy z)
  have hderiv (z : M) (v : TangentSpace (𝓡 n) z) :
      |mvfderiv (𝓡 n) f z v| ≤ K * g.tangentNorm z v := by
    have hcs : |mvfderiv (𝓡 n) f z v| ≤
        g.tangentNorm z (D.gradient f z) * g.tangentNorm z v := by
      rw [← D.inner_gradient]
      exact abs_real_inner_le_norm (D.gradient f z) v
    exact hcs.trans (mul_le_mul_of_nonneg_right (hnorm z) (Real.sqrt_nonneg _))
  exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound (hf.of_le (by simp))
    (show 0 < K from hA) hderiv p y

end PoincareConjecture.M47Positive
