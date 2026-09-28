import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.CoordinateGreen
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChartSupport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChangeOfVariables
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory VectorField
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem linearMap_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    L w = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * w i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr w)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm

theorem fderiv_chartPullback_coordinateGradient
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    fderiv ℝ (chartPullback e u) x
        (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) x) =
      g.inner (e x) (D.gradient u (e x)) (D.gradient v (e x)) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨hD.mfderiv hx, rfl⟩
  rw [(chartPullback_eventuallyEq e u hx).fderiv_eq, D.inner_gradient]
  have h := mvfderiv_comp x ((hu (e x)).mdifferentiableAt (by simp))
    (hD.mdifferentiableAt hx)
  have h' := congrArg (fun L => L (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) x)) h
  simp only [ContinuousLinearMap.comp_apply, mpullback, hinv.self_apply_inverse] at h'
  simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
    ContinuousLinearMap.comp_apply] at h'
  convert! h' using 1



theorem integral_chartPullback_mul_laplacian_density
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    (∫ x, chartPullback e u x * D.laplacian v (e x) * g.pullbackVolumeDensity e x) =
      -(∫ x in e.source,
        g.inner (e x) (D.gradient u (e x)) (D.gradient v (e x)) *
          g.pullbackVolumeDensity e x) := by
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    g.pullbackVolumeDensity e x *
      WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) x) i
  have hsource := tsupport_chartPullback_subset_source e hc hs
  have h := Poincare.integral_mul_coordinate_divergence
    ((contDiff_chartPullback e he hu hc hs).of_le (by simp))
    (hasCompactSupport_chartPullback e hc hs)
    (fun i x hx => (D.contDiffAt_coordinateGradientFlux e he hei
      (hsource hx) (hv (e x)) i).of_le (by simp))
  have hleft (x : EuclideanSpace ℝ (Fin n)) :
      chartPullback e u x * ∑ i, fderiv ℝ (V i) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) =
        chartPullback e u x * D.laplacian v (e x) * g.pullbackVolumeDensity e x := by
    by_cases hx : x ∈ e.source
    · rw [← D.density_mul_laplacian_eq_coordinate_divergence e he hei hx (hv (e x))]
      ring
    · simp [chartPullback, indicator_of_notMem hx]
  have hright (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i, fderiv ℝ (chartPullback e u) x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          V i x) = e.source.indicator (fun x =>
        g.inner (e x) (D.gradient u (e x)) (D.gradient v (e x)) *
          g.pullbackVolumeDensity e x) x := by
    by_cases hx : x ∈ e.source
    · rw [indicator_of_mem hx, ← D.fderiv_chartPullback_coordinateGradient e he hei hu hx,
        linearMap_eq_sum_coordinates, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [V]
      ring
    · rw [indicator_of_notMem hx]
      have heq : chartPullback e u =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hsource ht))
      have hz : fderiv ℝ (chartPullback e u) x = 0 := by
        rw [heq.fderiv_eq]
        simp
      simp [hz]
  change (∫ x, chartPullback e u x * ∑ i, fderiv ℝ (V i) x
    (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      -(∫ x, ∑ i, fderiv ℝ (chartPullback e u) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) * V i x) at h
  rw [integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hleft),
    integral_congr_ae (μ := volume) (Filter.Eventually.of_forall hright),
    integral_indicator e.open_source.measurableSet] at h
  exact h

end PoincareConjecture.LeviCivitaData
