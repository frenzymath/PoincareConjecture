import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.VectorField.Commutator
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Operator


















set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_orthonormal_changeBasis
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) (hxy : LinearIndependent ℝ ![x, y]) :
    ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧
      (inner ℝ (a • x + b • y) (a • x + b • y) : ℝ) = 1 ∧
      (inner ℝ (c • x + d • y) (c • x + d • y) : ℝ) = 1 ∧
      (inner ℝ (a • x + b • y) (c • x + d • y) : ℝ) = 0 := by
  classical
  have hx0 : x ≠ 0 := by
    intro h
    rw [linearIndependent_fin2] at hxy
    exact hxy.2 0 (by simp [h])
  have hxx : (0 : ℝ) < inner ℝ x x := real_inner_self_pos.2 hx0
  have hxxne : (inner ℝ x x : ℝ) ≠ 0 := ne_of_gt hxx
  set μ : ℝ := (inner ℝ x y : ℝ) / (inner ℝ x x : ℝ) with hμ
  set z : V := y - μ • x with hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [hz] at h
    exact ((LinearIndependent.pair_iff' hx0).mp hxy) μ (sub_eq_zero.mp h).symm
  have hzz : (0 : ℝ) < inner ℝ z z := real_inner_self_pos.2 hz0
  have hxz : (inner ℝ x z : ℝ) = 0 := by
    rw [hz, inner_sub_right, real_inner_smul_right, hμ,
      div_mul_cancel₀ _ hxxne, sub_self]
  set nx : ℝ := Real.sqrt (inner ℝ x x : ℝ)
  set nz : ℝ := Real.sqrt (inner ℝ z z : ℝ)
  have hnxpos : 0 < nx := Real.sqrt_pos.2 hxx
  have hnzpos : 0 < nz := Real.sqrt_pos.2 hzz
  have hnx2 : nx * nx = (inner ℝ x x : ℝ) := Real.mul_self_sqrt hxx.le
  have hnz2 : nz * nz = (inner ℝ z z : ℝ) := Real.mul_self_sqrt hzz.le
  have hxe : (nx⁻¹ • x + (0 : ℝ) • y) = nx⁻¹ • x := by simp
  have hye : (-(nz⁻¹ * μ) • x + nz⁻¹ • y) = nz⁻¹ • z := by
    rw [hz, smul_sub, smul_smul]
    module
  refine ⟨nx⁻¹, 0, -(nz⁻¹ * μ), nz⁻¹, ?_, ?_, ?_, ?_⟩
  · have hd : nx⁻¹ * nz⁻¹ - 0 * (-(nz⁻¹ * μ)) = nx⁻¹ * nz⁻¹ := by ring
    rw [hd]
    positivity
  · rw [hxe, real_inner_smul_left, real_inner_smul_right, ← hnx2]
    field_simp
  · rw [hye, real_inner_smul_left, real_inner_smul_right, ← hnz2]
    field_simp
  · rw [hxe, hye, real_inner_smul_left, real_inner_smul_right, hxz]
    ring





theorem curvatureTensor_diagonal_nonneg_of_orthonormal
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 ≤ D.sectionalCurvature x u v)
    (u v : TangentSpace (𝓡 n) x) :
    0 ≤ D.curvatureTensor x u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_cases hxy : LinearIndependent ℝ ![u, v]
  · obtain ⟨a, b, c, d, hdet, hp, hq, hpq⟩ :=
      exists_orthonormal_changeBasis u v hxy
    have hnum : D.curvatureTensor x (a • u + b • v) (c • u + d • v)
        (a • u + b • v) (c • u + d • v) =
        (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
      simp only [curvatureTensor_add_first, curvatureTensor_add_second,
        curvatureTensor_add_third, curvatureTensor_add_last,
        curvatureTensor_smul_first, curvatureTensor_smul_second,
        curvatureTensor_smul_third, curvatureTensor_smul_last,
        curvatureTensor_zero_first, curvatureTensor_zero_last]
      rw [curvatureTensor_swap_first, curvatureTensor_swap_last,
        D.curvatureTensor_swap_first x v u u v]
      ring
    have hh := hsec (a • u + b • v) (c • u + d • v) hp hq hpq
    unfold sectionalCurvature at hh
    change 0 ≤ D.curvatureTensor x (a • u + b • v) (c • u + d • v)
      (a • u + b • v) (c • u + d • v) /
      (inner ℝ (a • u + b • v) (a • u + b • v) *
        inner ℝ (c • u + d • v) (c • u + d • v) -
        inner ℝ (a • u + b • v) (c • u + d • v) ^ 2) at hh
    rw [hp, hq, hpq, hnum] at hh
    norm_num only [one_mul, zero_pow, sub_zero, div_one] at hh
    exact nonneg_of_mul_nonneg_right hh (sq_pos_of_ne_zero hdet)
  · rw [linearIndependent_fin2] at hxy
    by_cases hv : v = 0
    · rw [hv]
      have hz := D.curvatureTensor_smul_second x 0 u 0 u 0
      simpa only [zero_smul, zero_mul] using hz.ge
    · obtain ⟨c, hc⟩ : ∃ c : ℝ, c • v = u := by
        by_contra hn
        push Not at hn
        exact hxy ⟨hv, hn⟩
      rw [← hc, curvatureTensor_smul_first, curvatureTensor_zero_first]
      simp

end PoincareConjecture.LeviCivitaData
