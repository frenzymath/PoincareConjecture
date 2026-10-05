import PoincareLib.Geometry.Riemannian.Metric.Gradient
import PoincareLib.Geometry.Riemannian.ScalarOperators.Gradient

/-!
# Algebraic consequences of a parallel unit gradient

This file isolates the pointwise part of the parallel-gradient splitting
argument.  The global flow and product construction use these facts but do
not need to reproduce the metric-duality calculations.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Bundle

namespace PoincareMT

universe u

namespace RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The gradient has unit length in the retained Riemannian metric. -/
def HasUnitGradient (D : LeviCivitaData g) (f : M → ℝ) : Prop :=
  ∀ x, g.inner x (D.gradient f x) (D.gradient f x) = 1

/-- The scalar Hessian vanishes identically. -/
def HasZeroHessian (D : LeviCivitaData g) (f : M → ℝ) : Prop :=
  ∀ x u v, D.hessian f x u v = 0

theorem gradient_ne_zero_of_hasUnitGradient
    {D : LeviCivitaData g} {f : M → ℝ}
    (hunit : HasUnitGradient D f) (x : M) : D.gradient f x ≠ 0 := by
  intro hzero
  unfold HasUnitGradient at hunit
  have hunitx := hunit x
  rw [hzero] at hunitx
  simp at hunitx

theorem regular_of_hasUnitGradient
    {D : LeviCivitaData g} {f : M → ℝ}
  (hunit : HasUnitGradient D f) (x : M) :
    mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0 := by
  intro hzero
  have hgrad : D.gradient f x = 0 := by
    rw [D.gradient_eq_metric_gradient]
    exact (g.gradient_eq_zero_iff_mfderiv_eq_zero f x).2 hzero
  exact gradient_ne_zero_of_hasUnitGradient hunit x hgrad

theorem laplacian_eq_zero_of_hasZeroHessian
    {D : LeviCivitaData g} {f : M → ℝ}
    (hzero : HasZeroHessian D f) (x : M) : D.laplacian f x = 0 := by
  unfold LeviCivitaData.laplacian
  apply Finset.sum_eq_zero
  intro i hi
  exact hzero x (g.orthonormalBasis x i) (g.orthonormalBasis x i)

theorem connection_gradient_eq_zero_of_hasZeroHessian
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hzero : HasZeroHessian D f) (x : M)
    (u : TangentSpace (𝓡 n) x) :
    D.connection (D.gradient f) x u = 0 := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [map_zero]
  rw [← D.hessian_eq_inner_connection_gradient (hf x) u v]
  exact hzero x u v

theorem gradient_orthogonal_of_level_tangent
    {D : LeviCivitaData g} {f : M → ℝ} (x : M)
    {v : TangentSpace (𝓡 n) x}
    (hv : mvfderiv (𝓡 n) f x v = 0) :
    g.inner x (D.gradient f x) v = 0 := by
  rw [D.inner_gradient]
  exact hv

end RiemannianMetric

end PoincareMT
