import PoincareLib.Geometry.Riemannian.Measure.Coarea.Gram
import PoincareLib.Geometry.Riemannian.Measure.Density
import PoincareLib.Geometry.Riemannian.Metric.Gradient

/-!
# Coarea density in level coordinates

For a regular coordinate parametrization whose first coordinate is the level
function, the ambient volume density multiplied by the gradient norm equals
the Gram density of the remaining coordinate vectors.
-/

set_option autoImplicit false

open Filter Module
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]

/-- The tangential Gram density of a parametrization, with the first coordinate
held fixed. -/
noncomputable def levelCoordinateDensity (g : RiemannianMetric (n + 1) M)
    (e : EuclideanSpace ℝ (Fin (n + 1)) → M)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  Real.sqrt (Matrix.of (fun i j : Fin n => g.inner (e x)
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i.succ))
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j.succ)))).det

/-- The Gram identity applied to the differential of a regular parametrization.
The vector `z` is dual to its first coordinate. -/
theorem pullbackVolumeDensity_mul_tangentNorm
    (g : RiemannianMetric (n + 1) M)
    (e : EuclideanSpace ℝ (Fin (n + 1)) → M)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (he : Function.Bijective (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x))
    (z : TangentSpace (𝓡 (n + 1)) (e x))
    (hz : ∀ v : EuclideanSpace ℝ (Fin (n + 1)),
      g.inner (e x) z (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x v) = v 0) :
    g.pullbackVolumeDensity e x * g.tangentNorm (e x) z =
      g.levelCoordinateDensity e x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := LinearEquiv.ofBijective
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x).toLinearMap he
  let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.map A
  have hdual : ∀ i, ⟪z, b i⟫_ℝ = if i = 0 then 1 else 0 := by
    intro i
    change g.inner (e x) z
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x
        (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)) = _
    rw [hz]
    simp [EuclideanSpace.basisFun_apply, eq_comm]
  exact Poincare.Coarea.sqrt_gram_det_mul_norm_dual b z hdual

end PoincareMT.RiemannianMetric

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)

/-- In level coordinates, the gradient is the metric dual of the first
coordinate differential. -/
theorem inner_gradient_levelCoordinates
    {e : EuclideanSpace ℝ (Fin (n + 1)) → M} {f : M → ℝ}
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (he : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) e x)
    (hf : MDifferentiableAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (e x))
    (hlevel : (fun y => f (e y)) =ᶠ[𝓝 x] fun y => y 0)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    g.inner (e x) (g.gradient f (e x))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x v) = v 0 := by
  rw [g.inner_gradient]
  have h := congrArg (fun L => L v) (mvfderiv_comp x hf he)
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at h
  change fderiv ℝ (fun y => f (e y)) x v =
    mvfderiv (𝓡 (n + 1)) f (e x)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x v) at h
  have hd : fderiv ℝ (fun y => f (e y)) x = PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) 0 := by
    rw [hlevel.fderiv_eq]
    exact (PiLp.proj 2 (fun _ : Fin (n + 1) => ℝ) 0).fderiv
  rw [hd] at h
  exact h.symm

/-- The local coarea factor is the actual retained metric gradient norm. -/
theorem pullbackVolumeDensity_mul_gradient_norm
    {e : EuclideanSpace ℝ (Fin (n + 1)) → M} {f : M → ℝ}
    {x : EuclideanSpace ℝ (Fin (n + 1))}
    (he : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) e x)
    (hf : MDifferentiableAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (e x))
    (hi : Function.Bijective (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x))
    (hlevel : (fun y => f (e y)) =ᶠ[𝓝 x] fun y => y 0) :
    g.pullbackVolumeDensity e x * g.tangentNorm (e x) (g.gradient f (e x)) =
      g.levelCoordinateDensity e x :=
  g.pullbackVolumeDensity_mul_tangentNorm e x hi (g.gradient f (e x))
    (g.inner_gradient_levelCoordinates he hf hlevel)

end PoincareMT.RiemannianMetric
