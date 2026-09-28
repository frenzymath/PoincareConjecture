import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Gram
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient








set_option autoImplicit false

open Filter Module
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]



noncomputable def levelCoordinateDensity (g : RiemannianMetric (n + 1) M)
    (e : EuclideanSpace ℝ (Fin (n + 1)) → M)
    (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  Real.sqrt (Matrix.of (fun i j : Fin n => g.inner (e x)
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i.succ))
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e x
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ j.succ)))).det



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

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)



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

end PoincareConjecture.RiemannianMetric
