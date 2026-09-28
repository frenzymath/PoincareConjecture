import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem rescaledMetric_gradient_scaledFunction
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (a : ℝ) (f : M → ℝ) (x : M) :
    (rescaledMetric g c hc).gradient (fun y => a * f y) x =
      (a / c) • g.gradient f x := by
  apply ((rescaledMetric g c hc).inner_isInvertible x).injective
  ext v
  rw [RiemannianMetric.inner_gradient, rescaledMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul, g.inner_gradient,
    mvfderiv_const_mul]
  field_simp

theorem rescaledMetric_gradient_sqrt_mul
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (f : M → ℝ) (x : M) :
    (rescaledMetric g c hc).gradient (fun y => Real.sqrt c * f y) x =
      (Real.sqrt c)⁻¹ • g.gradient f x := by
  rw [rescaledMetric_gradient_scaledFunction]
  congr 1
  have hs := Real.sq_sqrt hc.le
  have hsn : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  field_simp
  exact hs

theorem rescaledMetric_inner_normalized
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (rescaledMetric g c hc).inner x
      ((Real.sqrt c)⁻¹ • v) ((Real.sqrt c)⁻¹ • w) = g.inner x v w := by
  rw [rescaledMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hs := Real.sq_sqrt hc.le
  have hsn : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  field_simp
  rw [hs]

theorem rescaledMetric_tangentNorm_normalized
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (rescaledMetric g c hc).tangentNorm x ((Real.sqrt c)⁻¹ • v) =
      g.tangentNorm x v := by
  unfold RiemannianMetric.tangentNorm
  rw [rescaledMetric_inner_normalized]

theorem rescaledMetric_inner_gradient_sqrt_mul
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (f h : M → ℝ) (x : M) :
    (rescaledMetric g c hc).inner x
      ((rescaledMetric g c hc).gradient (fun y => Real.sqrt c * f y) x)
      ((rescaledMetric g c hc).gradient (fun y => Real.sqrt c * h y) x) =
      g.inner x (g.gradient f x) (g.gradient h x) := by
  rw [rescaledMetric_gradient_sqrt_mul, rescaledMetric_gradient_sqrt_mul,
    rescaledMetric_inner_normalized]

theorem rescaledMetric_tangentNorm_gradient_sqrt_mul
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c)
    (f : M → ℝ) (x : M) :
    (rescaledMetric g c hc).tangentNorm x
      ((rescaledMetric g c hc).gradient (fun y => Real.sqrt c * f y) x) =
      g.tangentNorm x (g.gradient f x) := by
  rw [rescaledMetric_gradient_sqrt_mul, rescaledMetric_tangentNorm_normalized]

theorem rescaledMetric_hessian_const_mul
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c)
    (a : ℝ) (f : M → ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    (rescaledMetric_connection g D c hc).hessian (fun y => a * f y) x v w =
      a * D.hessian f x v w := by
  exact D.hessian_const_mul a f x v w

theorem rescaledMetric_hessian_sqrt_mul_le
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (c : ℝ) (hc : 0 < c)
    (f : M → ℝ) (x : M) (v : TangentSpace (𝓡 n) x) (β : ℝ)
    (h : D.hessian f x v v ≤ β * g.inner x v v) :
    (rescaledMetric_connection g D c hc).hessian
      (fun y => Real.sqrt c * f y) x v v ≤
      (β / Real.sqrt c) * (rescaledMetric g c hc).inner x v v := by
  rw [rescaledMetric_hessian_const_mul, rescaledMetric_inner]
  calc
    _ ≤ Real.sqrt c * (β * g.inner x v v) :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg c)
    _ = _ := by
      have hs := Real.sq_sqrt hc.le
      have hsn : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
      field_simp
      nlinarith [congrArg (fun t => t * (β * g.inner x v v)) hs]

end PoincareConjecture
