import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Density







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def tangentVolumeDensity (g : RiemannianMetric n M) (x : M) : ℝ :=
  Real.sqrt (Matrix.of (fun i j : Fin n => g.inner x
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))).det

def relativeVolumeDensity (g h : RiemannianMetric n M) (x : M) : ℝ :=
  g.tangentVolumeDensity x / h.tangentVolumeDensity x

theorem tangentVolumeDensity_pos (g : RiemannianMetric n M) (x : M) :
    0 < g.tangentVolumeDensity x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) x := LinearMap.id
  apply Real.sqrt_pos.mpr
  change 0 < (Matrix.gram ℝ (fun i : Fin n => A
    (EuclideanSpace.basisFun (Fin n) ℝ i))).det
  exact (Matrix.posDef_gram_of_linearIndependent
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.map' A
      (LinearMap.ker_eq_bot.mpr (fun _ _ h => h)))).det_pos

theorem relativeVolumeDensity_pos (g h : RiemannianMetric n M) (x : M) :
    0 < g.relativeVolumeDensity h x :=
  div_pos (g.tangentVolumeDensity_pos x) (h.tangentVolumeDensity_pos x)

theorem pullbackVolumeDensity_eq_det_mul_tangentVolumeDensity
    (g : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) :
    g.pullbackVolumeDensity f x =
      |(mfderiv (𝓡 n) (𝓡 n) f x).det| * g.tangentVolumeDensity (f x) := by
  classical
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  let B := (g.inner (f x)).toBilinForm
  have hB : Matrix.of (fun i j : Fin n => g.inner (f x)
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      (LinearMap.BilinForm.toMatrix b) B := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  have hBT : Matrix.of (fun i j : Fin n => g.inner (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (mfderiv (𝓡 n) (𝓡 n) f x (EuclideanSpace.basisFun (Fin n) ℝ j))) =
      (LinearMap.BilinForm.toMatrix b) (B.comp T T) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  unfold pullbackVolumeDensity tangentVolumeDensity
  rw [hB, hBT, LinearMap.BilinForm.toMatrix_comp b b,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
  change Real.sqrt (T.det * ((LinearMap.BilinForm.toMatrix b) B).det * T.det) = _
  rw [show T.det * ((LinearMap.BilinForm.toMatrix b) B).det * T.det =
      T.det ^ 2 * ((LinearMap.BilinForm.toMatrix b) B).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

theorem relativeVolumeDensity_eq_pullback_div
    (g h : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n))
    (hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    g.relativeVolumeDensity h (f x) =
      g.pullbackVolumeDensity f x / h.pullbackVolumeDensity f x := by
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  have hdet : T.det ≠ 0 := fun hzero =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hi)
  rw [g.pullbackVolumeDensity_eq_det_mul_tangentVolumeDensity,
    h.pullbackVolumeDensity_eq_det_mul_tangentVolumeDensity]
  change g.tangentVolumeDensity (f x) / h.tangentVolumeDensity (f x) =
    (|T.det| * g.tangentVolumeDensity (f x)) / (|T.det| * h.tangentVolumeDensity (f x))
  field_simp [abs_ne_zero.mpr hdet, (h.tangentVolumeDensity_pos (f x)).ne']

end PoincareConjecture.RiemannianMetric
