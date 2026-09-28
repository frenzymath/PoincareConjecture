import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Contractions
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.TangentIsometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Homothety

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N]

theorem homothety_ricci_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D'.ricci (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) =
      D.ricci x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let e := homothetyTangentIsometry g h f Q hQ hf x
  rw [ricci_eq_sum_basis D' (f x) (b.map e)]
  change (∑ i, D'.curvatureTensor (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
    (e (b i)) (mfderiv (𝓡 n) (𝓡 n) f x v) (e (b i))) =
      ∑ i, D.curvatureTensor x u (b i) v (b i)
  apply Finset.sum_congr rfl
  intro i _
  change curvatureTensorLinear D' (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x (b i))
    (mfderiv (𝓡 n) (𝓡 n) f x v)
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x (b i)) = _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, curvatureTensorLinear_apply]
  rw [homothety_curvatureTensor_eq g h f Q hf D D']
  simp only [← mul_assoc, inv_sqrt_mul_inv_sqrt Q hQ.le, inv_mul_cancel₀ hQ.ne', one_mul]

theorem homothety_scalarCurvature_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) : D'.scalarCurvature (f x) = D.scalarCurvature x / Q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let e := homothetyTangentIsometry g h f Q hQ hf x
  rw [scalarCurvature_eq_sum_basis D' (f x) (b.map e)]
  change (∑ i, D'.ricci (f x) (e (b i)) (e (b i))) =
    (∑ i, D.ricci x (b i) (b i)) / Q
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change ricciLinear D' (f x) ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x (b i))
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x (b i)) = _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ricciLinear_apply]
  rw [homothety_ricci_eq g h f Q hQ hf D D', ← mul_assoc,
    inv_sqrt_mul_inv_sqrt Q hQ.le, div_eq_mul_inv, mul_comm]

theorem homothety_curvatureTensor_normalized
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    D'.curvatureTensor (f x) (homothetyTangentIsometry g h f Q hQ hf x u)
      (homothetyTangentIsometry g h f Q hQ hf x v)
      (homothetyTangentIsometry g h f Q hQ hf x w)
      (homothetyTangentIsometry g h f Q hQ hf x z) = D.curvatureTensor x u v w z / Q := by
  change curvatureTensorLinear D' (f x)
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x u)
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x v)
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x w)
    ((Real.sqrt Q)⁻¹ • mfderiv (𝓡 n) (𝓡 n) f x z) = _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, curvatureTensorLinear_apply]
  rw [homothety_curvatureTensor_eq g h f Q hf D D']
  calc
    (Real.sqrt Q)⁻¹ * ((Real.sqrt Q)⁻¹ * ((Real.sqrt Q)⁻¹ *
        ((Real.sqrt Q)⁻¹ * (Q * D.curvatureTensor x u v w z)))) =
        ((Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹) *
          ((Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹) * Q * D.curvatureTensor x u v w z := by ring
    _ = Q⁻¹ * (Q⁻¹ * Q) * D.curvatureTensor x u v w z := by
      rw [inv_sqrt_mul_inv_sqrt Q hQ.le, mul_assoc Q⁻¹ Q⁻¹ Q]
    _ = D.curvatureTensor x u v w z / Q := by
      rw [inv_mul_cancel₀ hQ.ne', mul_one, div_eq_mul_inv, mul_comm]

theorem homothety_curvatureTensorNorm_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) : D'.curvatureTensorNorm (f x) = D.curvatureTensorNorm x / Q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let e := homothetyTangentIsometry g h f Q hQ hf x
  rw [curvatureTensorNorm_eq_sqrt_sum_basis D' (f x) (b.map e)]
  change Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (D'.curvatureTensor (f x) (e (b i)) (e (b j)) (e (b k)) (e (b l))) ^ 2) = _
  simp only [e, homothety_curvatureTensor_normalized g h f Q hQ hf D D',
    div_pow, ← Finset.sum_div]
  rw [Real.sqrt_div' _ (sq_nonneg Q), Real.sqrt_sq hQ.le]
  rfl

theorem homothety_curvatureTensorNorm_sq_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) : (D'.curvatureTensorNorm (f x)) ^ 2 = (D.curvatureTensorNorm x) ^ 2 / Q ^ 2 := by
  rw [homothety_curvatureTensorNorm_eq g h f Q hQ hf D D', div_pow]

theorem homothety_curvature_bound_iff
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (E : Set M) (K : ℝ) :
    (∀ y ∈ f '' E, D'.curvatureTensorNorm y ≤ K / Q) ↔
      ∀ x ∈ E, D.curvatureTensorNorm x ≤ K := by
  constructor
  · intro hbound x hx
    have H := hbound (f x) ⟨x, hx, rfl⟩
    rw [homothety_curvatureTensorNorm_eq g h f Q hQ hf D D'] at H
    exact (div_le_div_iff_of_pos_right hQ).mp H
  · rintro hbound _ ⟨x, hx, rfl⟩
    rw [homothety_curvatureTensorNorm_eq g h f Q hQ hf D D']
    exact (div_le_div_iff_of_pos_right hQ).mpr (hbound x hx)

theorem homothety_nonflat_iff
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h) :
    (∃ y : N, D'.curvatureTensorNorm y ≠ 0) ↔ ∃ x : M, D.curvatureTensorNorm x ≠ 0 := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := f.surjective y
    change D'.curvatureTensorNorm (f x) ≠ 0 at hy
    rw [homothety_curvatureTensorNorm_eq g h f Q hQ hf D D'] at hy
    exact ⟨x, fun hx ↦ hy (by rw [hx, zero_div])⟩
  · rintro ⟨x, hx⟩
    refine ⟨f x, ?_⟩
    rw [homothety_curvatureTensorNorm_eq g h f Q hQ hf D D']
    exact div_ne_zero hx hQ.ne'

end PoincareConjecture.Homothety
