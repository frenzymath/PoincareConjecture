import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Orthonormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Differential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M28.tube

private abbrev E := EuclideanSpace ℝ (Fin 3)

private theorem gauss_coefficients_at_zero
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E}
    (hB : DifferentiableAt ℝ B 0) (hU : U ∈ 𝓝 (0 : E))
    (hgauss : ∀ x ∈ U, ∀ w, B x x w = inner ℝ x w) (v w : E) :
    B 0 v w = inner ℝ v w := by
  have hd := ((hB.hasFDerivAt.clm_apply (hasFDerivAt_id (0 : E))).clm_apply
    (hasFDerivAt_const w 0)).fderiv
  have heq : (fun x => B x x w) =ᶠ[𝓝 (0 : E)] (innerSL ℝ).flip w := by
    filter_upwards [hU] with x hx
    exact hgauss x hx w
  simp only [id_eq] at hd
  rw [heq.fderiv_eq, ContinuousLinearMap.fderiv] at hd
  have hv := congrArg (fun L => L v) hd
  simpa only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_zero, zero_add,
    innerSL_apply_apply, ContinuousLinearMap.flip_apply, map_zero,
    zero_apply, add_zero] using hv.symm

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem invertible_differential_of_smooth_partial_homeomorph
    (f : OpenPartialHomeomorph E M)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source)
    (hf' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target)
    {x : E} (hx : x ∈ f.source) :
    (mfderiv (𝓡 3) (𝓡 3) f x).IsInvertible := by
  have hdf := (hf.contMDiffAt (f.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdi := (hf'.contMDiffAt
    (f.open_target.mem_nhds (f.map_source hx))).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x hdi hdf
  have hid : (f.symm ∘ f) =ᶠ[𝓝 x] (id : E → E) := by
    filter_upwards [f.open_source.mem_nhds hx] with y hy
    exact f.left_inv hy
  have hleft : (mfderiv (𝓡 3) (𝓡 3) f.symm (f x)).comp
      (mfderiv (𝓡 3) (𝓡 3) f x) = ContinuousLinearMap.id ℝ E := by
    rw [← hcomp, hid.mfderiv_eq, mfderiv_id]
    ext v
    rfl
  apply RiemannianMetric.isInvertible_mfderiv_of_injective
  intro v w hvw
  have hv := congrArg (fun L : E →L[ℝ] E => L v) hleft
  have hw := congrArg (fun L : E →L[ℝ] E => L w) hleft
  exact hv.symm.trans ((congrArg
    (mfderiv (𝓡 3) (𝓡 3) f.symm (f x)) hvw).trans hw)

theorem exists_normalized_gauss_parametrization
    (g : RiemannianMetric 3 M) (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∃ e : E → M,
      e 0 = p ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R) ∧
      (∀ x ∈ ball 0 R, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) ∧
      (∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w) ∧
      (∀ x ∈ ball 0 R, ∀ w, g.pullbackCoefficients e x x w = inner ℝ x w) := by
  obtain ⟨f, hf0, hfp, hf, hf', hgauss, _⟩ := g.exists_exponential_chart_gauss p
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  have hLmetric (v w : E) : g.inner p (L v) (L w) = inner ℝ v w := by
    simpa only [g.chartCoefficients_center] using hL v w
  let V : Set E := L ⁻¹' f.source
  have hV : V ∈ 𝓝 (0 : E) := by
    exact L.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [map_zero] using f.open_source.mem_nhds hf0)
  obtain ⟨R, hR, hRV⟩ := Metric.mem_nhds_iff.mp hV
  let e : E → M := f ∘ L
  have hLsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ L :=
    contMDiff_iff_contDiff.mpr L.contDiff
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R) :=
    hf.comp hLsmooth.contMDiffOn hRV
  have hder (x : E) (hx : x ∈ ball 0 R) :
      mfderiv (𝓡 3) (𝓡 3) e x =
        (mfderiv (𝓡 3) (𝓡 3) f (L x)).comp L.toContinuousLinearMap := by
    have h := mfderiv_comp x
      ((hf.contMDiffAt (f.open_source.mem_nhds (hRV hx))).mdifferentiableAt (by simp))
      ((hLsmooth x).mdifferentiableAt (by simp))
    simpa only [ContinuousLinearEquiv.mfderiv_eq] using h
  have hi (x : E) (hx : x ∈ ball 0 R) :
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible := by
    apply RiemannianMetric.isInvertible_mfderiv_of_injective
    rw [hder x hx]
    exact (invertible_differential_of_smooth_partial_homeomorph f hf hf'
      (hRV hx)).injective.comp L.injective
  have hGauss (x : E) (hx : x ∈ ball 0 R) (w : E) :
      g.pullbackCoefficients e x x w = inner ℝ x w := by
    change g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x x)
      (mfderiv (𝓡 3) (𝓡 3) e x w) = _
    rw [hder x hx]
    exact (hgauss (L x) (hRV hx) (L w)).trans (hLmetric x w)
  have hcenter : ∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w := by
    apply gauss_coefficients_at_zero
      ((g.contDiffAt_pullbackCoefficients
        (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR)))).differentiableAt
          (by simp))
      (isOpen_ball.mem_nhds (mem_ball_self hR)) hGauss
  refine ⟨R, hR, e, ?_, he, hi, hcenter, hGauss⟩
  simpa only [e, Function.comp_apply, map_zero] using hfp

end PoincareConjecture.M28.tube
