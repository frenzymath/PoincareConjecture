import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLocalHarmonic














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem exists_local_annular_isothermal_chart (g : RiemannianMetric 2 Plane) (p : Plane) :
    ∃ (e : OpenPartialHomeomorph Plane Plane) (a : Plane) (lambda : Plane → ℝ),
      a ∈ e.source ∧ e a = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ lambda e.source ∧
      (∀ x ∈ e.source, 0 < lambda x) ∧
      ∀ x ∈ e.source, ∀ v w : Plane,
        g.pullbackCoefficients e x v w = lambda x * inner ℝ v w := by
  obtain ⟨f, r, h, Dh, hr, hf0, hf, hfi, hmetric, hharm⟩ :=
    exists_local_annular_harmonic_chart g p
  have hzero : (0 : Plane) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  obtain ⟨c, hc0, hcsub, hceq, hcs, hcis⟩ :=
    M60.exists_local_smooth_inverse_surface f Metric.isOpen_ball hf hfi hzero
  obtain ⟨d, hd0, hdsub, hds, hdis, hdmetric⟩ :=
    M60.exists_isothermal_coordinates_of_harmonic h Dh Metric.isOpen_ball
      ((convex_ball (0 : Plane) r).starConvex hzero) hzero (fun x hx => hharm x hx 0)
  let e : OpenPartialHomeomorph Plane Plane := d.symm.trans c
  let P : Plane → ℝ := fun x => M60.firstCoordinateGradient h Dh x 0
  let lambda : Plane → ℝ := fun x => (P (d.symm x))⁻¹
  have he0 : d 0 ∈ e.source := by
    refine ⟨d.map_source hd0, ?_⟩
    change d.symm (d 0) ∈ c.source
    rwa [d.left_inv hd0]
  have hP : ContDiff ℝ ∞ P := by
    apply (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff.comp
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact Dh.contDiffAt_gradient_euclidean
      (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff.contDiffAt
  have hPpos (x : Plane) : 0 < P x := M60.firstCoordinateGradient_zero_pos h Dh x
  refine ⟨e, d 0, lambda, he0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change c (d.symm (d 0)) = p
    rw [d.left_inv hd0, hceq hc0, hf0]
  · change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (c ∘ d.symm) e.source
    exact hcs.comp ((contMDiffOn_iff_contDiffOn.mpr hdis).mono (fun _ hx => hx.1))
      (fun _ hx => hx.2)
  · change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (d ∘ c.symm) e.target
    exact (contMDiff_iff_contDiff.mpr hds).comp_contMDiffOn
      (hcis.mono (fun _ hx => hx.1))
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    exact (hP.contDiffAt.comp x (hdis.contDiffAt (d.open_target.mem_nhds hx.1))).inv
      (hPpos (d.symm x)).ne'
  · intro x _
    exact inv_pos.mpr (hPpos (d.symm x))
  · intro x hx v w
    have hz := hdsub (d.map_target hx.1)
    have hfd := (hf.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp)
    have hdi := (hdis.contDiffAt (d.open_target.mem_nhds hx.1)).differentiableAt (by simp)
    have heq : f ∘ d.symm =ᶠ[𝓝 x] (e : Plane → Plane) := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      exact (hceq hy.2).symm
    rw [← g.pullbackCoefficients_comp_of_eventuallyEq hfd hdi heq v w,
      ← hmetric (d.symm x) hz]
    change h.inner (d.symm x) (fderiv ℝ d.symm x v) (fderiv ℝ d.symm x w) = _
    obtain ⟨hInv, hmetric'⟩ := hdmetric (d.symm x) (d.map_target hx.1)
    rw [hmetric']
    obtain ⟨L, hL⟩ := hInv
    have hdL : HasFDerivAt d (L : Plane →L[ℝ] Plane) (d.symm x) := by
      rw [hL]
      exact (hds.differentiable (by simp) _).hasFDerivAt
    rw [(d.hasFDerivAt_symm hx.1 hdL).fderiv, ← hL]
    simp only [ContinuousLinearEquiv.coe_coe, L.apply_symm_apply]
    rfl

end PoincareConjecture.M64Uniformization
