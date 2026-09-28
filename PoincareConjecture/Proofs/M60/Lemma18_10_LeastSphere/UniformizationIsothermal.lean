import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationHarmonicCompact
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationIsothermalPlane
import PoincareConjecture.Proofs.M60.Mathlib.UniformizationLocalInverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

universe u

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {M : Type u} [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [ChartedSpace Plane M] [IsManifold (𝓡 2) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem exists_isothermal_chart_compact_surface
    (g : RiemannianMetric 2 M) (D : LeviCivitaData g) (p : M) :
    ∃ (e : OpenPartialHomeomorph Plane M) (a : Plane) (lambda : Plane → ℝ),
      a ∈ e.source ∧ e a = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ContDiffOn ℝ ∞ lambda e.source ∧
      (∀ x ∈ e.source, 0 < lambda x) ∧
      ∀ x ∈ e.source, ∀ v w : Plane,
        g.pullbackCoefficients e x v w = lambda x * inner ℝ v w := by
  obtain ⟨r, C, H, hr, -, -, ⟨F⟩⟩ := exists_harmonic_lift_compact_surface g D p
  have hzero : (0 : Plane) ∈ Metric.ball 0 (2 * r) := Metric.mem_ball_self (by positivity)
  obtain ⟨c, hc0, hcsub, hceq, hcs, hcis⟩ :=
    exists_local_smooth_inverse_surface F.e Metric.isOpen_ball F.he F.hlocal hzero
  obtain ⟨d, hd0, hdsub, hds, hdis, hdmetric⟩ :=
    exists_isothermal_coordinates_of_harmonic F.h F.D' Metric.isOpen_ball
      ((convex_ball (0 : Plane) (2 * r)).starConvex hzero) hzero
      (fun x hx => F.hharmonic x hx 0)
  let e : OpenPartialHomeomorph Plane M := d.symm.trans c
  let P : Plane → ℝ := fun x => firstCoordinateGradient F.h F.D' x 0
  let lambda : Plane → ℝ := fun x => (P (d.symm x))⁻¹
  have he0 : d 0 ∈ e.source := by
    refine ⟨d.map_source hd0, ?_⟩
    change d.symm (d 0) ∈ c.source
    rwa [d.left_inv hd0]
  have hP : ContDiff ℝ ∞ P := by
    apply (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff.comp
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact F.D'.contDiffAt_gradient_euclidean
      (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff.contDiffAt
  have hPpos (x : Plane) : 0 < P x := firstCoordinateGradient_zero_pos F.h F.D' x
  refine ⟨e, d 0, lambda, he0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change c (d.symm (d 0)) = p
    rw [d.left_inv hd0, hceq hc0, F.he0]
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
    have hFi := (F.he.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)).mdifferentiableAt
      (by simp)
    have hdi := (hdis.contDiffAt (d.open_target.mem_nhds hx.1)).differentiableAt (by simp)
    have heq : F.e ∘ d.symm =ᶠ[𝓝 x] (e : Plane → M) := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      exact (hceq hy.2).symm
    rw [← g.pullbackCoefficients_comp_of_eventuallyEq hFi hdi heq v w,
      ← F.hpullback (d.symm x) hz]
    change F.h.inner (d.symm x) (fderiv ℝ d.symm x v) (fderiv ℝ d.symm x w) = _
    obtain ⟨hInv, hmetric⟩ := hdmetric (d.symm x) (d.map_target hx.1)
    rw [hmetric]
    obtain ⟨L, hL⟩ := hInv
    have hdL : HasFDerivAt d (L : Plane →L[ℝ] Plane) (d.symm x) := by
      rw [hL]
      exact (hds.differentiable (by simp) _).hasFDerivAt
    rw [(d.hasFDerivAt_symm hx.1 hdL).fderiv, ← hL]
    simp only [ContinuousLinearEquiv.coe_coe, L.apply_symm_apply]
    rfl

end PoincareConjecture.M60

end
