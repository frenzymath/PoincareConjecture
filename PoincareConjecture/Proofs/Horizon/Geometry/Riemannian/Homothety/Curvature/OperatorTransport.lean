import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.OperatorBasis
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.ContractionTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic











set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.Homothety

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T2Space N]


theorem homothety_curvatureOperatorQuadratic_basis
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    ∀ A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ,
      fourLinearQuadratic (curvatureTensorLinear D' (f x))
        ((g.orthonormalBasis x).map (homothetyTangentIsometry g h f Q hQ hf x)) A =
          D.curvatureOperatorQuadratic x A / Q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  intro A
  unfold fourLinearQuadratic
  simp only [OrthonormalBasis.map_apply, curvatureTensorLinear_apply,
    homothety_curvatureTensor_normalized g h f Q hQ hf D D',
    ← mul_div_assoc, ← Finset.sum_div]
  rfl


theorem homothety_nonnegative_operator_iff
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) : D'.NonnegativeCurvatureOperator (f x) ↔ D.NonnegativeCurvatureOperator x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) (f x)
  let b := (g.orthonormalBasis x).map (homothetyTangentIsometry g h f Q hQ hf x)
  unfold LeviCivitaData.NonnegativeCurvatureOperator LeviCivitaData.IsSkewCoefficient
  change (∀ A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) (f x))) →
    Fin (Module.finrank ℝ (TangentSpace (𝓡 n) (f x))) → ℝ,
    (∀ i j, A i j = -A j i) →
      0 ≤ fourLinearQuadratic (curvatureTensorLinear D' (f x)) (h.orthonormalBasis (f x)) A) ↔ _
  rw [fourLinear_nonnegative_basis_iff (curvatureTensorLinear D' (f x))
    (h.orthonormalBasis (f x)) b]
  simp only [b, homothety_curvatureOperatorQuadratic_basis g h f Q hQ hf D D',
    le_div_iff₀ hQ, zero_mul]


theorem homothety_operator_bound_iff
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (K : ℝ) (x : M) : D'.CurvatureOperatorBound (K / Q) (f x) ↔ D.CurvatureOperatorBound K x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) (f x)
  let b := (g.orthonormalBasis x).map (homothetyTangentIsometry g h f Q hQ hf x)
  unfold LeviCivitaData.CurvatureOperatorBound LeviCivitaData.IsSkewCoefficient
  change (∀ A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) (f x))) →
    Fin (Module.finrank ℝ (TangentSpace (𝓡 n) (f x))) → ℝ,
    (∀ i j, A i j = -A j i) →
      |fourLinearQuadratic (curvatureTensorLinear D' (f x)) (h.orthonormalBasis (f x)) A| ≤
        K / Q * ∑ i, ∑ j, (A i j) ^ 2) ↔ _
  rw [fourLinear_bound_basis_iff (curvatureTensorLinear D' (f x))
    (h.orthonormalBasis (f x)) b (K / Q)]
  simp only [b, homothety_curvatureOperatorQuadratic_basis g h f Q hQ hf D D',
    abs_div, abs_of_pos hQ, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hQ]

end PoincareConjecture.Homothety
