import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.BasisContractions

set_option autoImplicit false

open scoped BigOperators RealInnerProductSpace

namespace PoincareConjecture.Homothety

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem sum_fourlinear_mul_basis_eq
    (T U : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, ∑ k, ∑ l, T (b i) (b j) (b k) (b l) * U (b i) (b j) (b k) (b l)) =
      ∑ i, ∑ j, ∑ k, ∑ l, T (c i) (c j) (c k) (c l) * U (c i) (c j) (c k) (c l) := by
  have H := sum_sq_fourlinear_basis_eq (T + U) b c
  simp only [LinearMap.add_apply, add_sq, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum] at H
  rw [sum_sq_fourlinear_basis_eq T b c, sum_sq_fourlinear_basis_eq U b c] at H
  linarith

def bilinearSquare (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v ↦ B u v • B)
    (fun u u' v ↦ by simp [add_smul])
    (fun a u v ↦ by simp [smul_smul])
    (fun u v v' ↦ by simp [add_smul])
    (fun a u v ↦ by simp [smul_smul])

omit [FiniteDimensional ℝ E] in
theorem bilinearSquare_apply (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (u v w z : E) :
    bilinearSquare B u v w z = B u v * B w z := rfl

noncomputable def coefficientBilinear (b : OrthonormalBasis ι ℝ E) (A : ι → ι → ℝ) :
    E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • ((innerₗ E (b i)).smulRight (innerₗ E (b j)))

omit [FiniteDimensional ℝ E] in
theorem coefficientBilinear_apply_basis (b : OrthonormalBasis ι ℝ E)
    (A : ι → ι → ℝ) (i j : ι) : coefficientBilinear b A (b i) (b j) = A i j := by
  classical
  simp [coefficientBilinear, b.inner_eq_ite]

omit [FiniteDimensional ℝ E] in
theorem coefficientBilinear_skew (b : OrthonormalBasis ι ℝ E) (A : ι → ι → ℝ)
    (hA : ∀ i j, A i j = -A j i) (u v : E) :
    coefficientBilinear b A u v = -coefficientBilinear b A v u := by
  have H : coefficientBilinear b A = -(coefficientBilinear b A).flip := by
    apply b.toBasis.ext
    intro i
    apply b.toBasis.ext
    intro j
    change coefficientBilinear b A (b i) (b j) = -coefficientBilinear b A (b j) (b i)
    rw [coefficientBilinear_apply_basis, coefficientBilinear_apply_basis]
    exact hA i j
  exact congrArg (fun B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ ↦ B u v) H

noncomputable def basisCoefficientChange (b : OrthonormalBasis ι ℝ E)
    (c : OrthonormalBasis κ ℝ E) (A : ι → ι → ℝ) : κ → κ → ℝ :=
  fun i j ↦ coefficientBilinear b A (c i) (c j)

omit [FiniteDimensional ℝ E] in
theorem basisCoefficientChange_skew (b : OrthonormalBasis ι ℝ E)
    (c : OrthonormalBasis κ ℝ E) (A : ι → ι → ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∀ i j, basisCoefficientChange b c A i j = -basisCoefficientChange b c A j i :=
  fun i j ↦ coefficientBilinear_skew b A hA (c i) (c j)

theorem basisCoefficientChange_norm_sq (b : OrthonormalBasis ι ℝ E)
    (c : OrthonormalBasis κ ℝ E) (A : ι → ι → ℝ) :
    (∑ i, ∑ j, (A i j) ^ 2) = ∑ i, ∑ j, (basisCoefficientChange b c A i j) ^ 2 := by
  simpa only [basisCoefficientChange, coefficientBilinear_apply_basis] using
    sum_sq_bilinear_basis_eq (coefficientBilinear b A) b c

noncomputable def fourLinearQuadratic
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (A : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * T (b i) (b j) (b k) (b l)

theorem fourLinearQuadratic_basis_change
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) (A : ι → ι → ℝ) :
    fourLinearQuadratic T b A = fourLinearQuadratic T c (basisCoefficientChange b c A) := by
  simpa only [fourLinearQuadratic, basisCoefficientChange, bilinearSquare_apply,
    coefficientBilinear_apply_basis] using
    sum_fourlinear_mul_basis_eq (bilinearSquare (coefficientBilinear b A)) T b c

theorem fourLinear_nonnegative_basis_iff
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∀ A : ι → ι → ℝ, (∀ i j, A i j = -A j i) → 0 ≤ fourLinearQuadratic T b A) ↔
      ∀ A : κ → κ → ℝ, (∀ i j, A i j = -A j i) → 0 ≤ fourLinearQuadratic T c A := by
  constructor
  · intro H A hA
    rw [fourLinearQuadratic_basis_change T c b A]
    exact H _ (basisCoefficientChange_skew c b A hA)
  · intro H A hA
    rw [fourLinearQuadratic_basis_change T b c A]
    exact H _ (basisCoefficientChange_skew b c A hA)

theorem fourLinear_bound_basis_iff
    (T : E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) (K : ℝ) :
    (∀ A : ι → ι → ℝ, (∀ i j, A i j = -A j i) →
      |fourLinearQuadratic T b A| ≤ K * ∑ i, ∑ j, (A i j) ^ 2) ↔
    ∀ A : κ → κ → ℝ, (∀ i j, A i j = -A j i) →
      |fourLinearQuadratic T c A| ≤ K * ∑ i, ∑ j, (A i j) ^ 2 := by
  constructor
  · intro H A hA
    rw [fourLinearQuadratic_basis_change T c b A, basisCoefficientChange_norm_sq c b A]
    exact H _ (basisCoefficientChange_skew c b A hA)
  · intro H A hA
    rw [fourLinearQuadratic_basis_change T b c A, basisCoefficientChange_norm_sq b c A]
    exact H _ (basisCoefficientChange_skew b c A hA)

end PoincareConjecture.Homothety
