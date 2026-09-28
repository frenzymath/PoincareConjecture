import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationIsothermal
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationConformalCurvature
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

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

theorem exists_conformal_euclidean_near_point
    (g : RiemannianMetric 2 M) (D : LeviCivitaData g) (p : M) :
    ∃ (F : M → ℝ) (hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ F)
      (e : OpenPartialHomeomorph Plane M) (a : Plane) (U : Set Plane),
      IsOpen U ∧ a ∈ U ∧ U ⊆ e.source ∧ e a = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ x ∈ U, ∀ v w : Plane,
        (M36.positiveScaling g (fun y => Real.exp (-2 * F y))
          (M36.contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)).pullbackCoefficients e x v w =
            inner ℝ v w := by
  obtain ⟨e, a, lambda, ha, hpa, hes, heis, hlam, hlpos, hmetric⟩ :=
    exists_isothermal_chart_compact_surface g D p
  have hp : p ∈ e.target := hpa ▸ e.map_source ha
  let f : M → ℝ := fun y => Real.log (lambda (e.symm y)) / 2
  have hf : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ f e.target := by
    intro y hy
    have hz := e.map_target hy
    have hlog := (hlam.contDiffAt (e.open_source.mem_nhds hz)).log (hlpos _ hz).ne'
    apply ContMDiffAt.contMDiffWithinAt
    exact ((contMDiffAt_iff_contDiffAt.mpr hlog).comp y
      (heis.contMDiffAt (e.open_target.mem_nhds hy))).div_const 2
  obtain ⟨chi, -, hchi⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 2) p).mem_iff.mp
    (e.open_target.mem_nhds hp)
  let F : M → ℝ := fun y => chi y * f y
  have hF : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ F := by
    apply contMDiff_of_tsupport
    intro y hy
    have hy' : y ∈ e.target := hchi (tsupport_mul_subset_left hy)
    exact chi.contMDiffAt.mul (hf.contMDiffAt (e.open_target.mem_nhds hy'))
  have hnear : F =ᶠ[𝓝 p] f := by
    filter_upwards [chi.eventuallyEq_one] with y hy
    change chi y * f y = f y
    rw [hy, Pi.one_apply, one_mul]
  have hEc : Tendsto e (𝓝 a) (𝓝 p) := by
    rw [← hpa]
    exact e.continuousAt ha
  have hlocal : ∀ᶠ x in 𝓝 a, x ∈ e.source ∧ F (e x) = Real.log (lambda x) / 2 := by
    filter_upwards [hnear.comp_tendsto hEc, e.open_source.mem_nhds ha] with x hx hxs
    refine ⟨hxs, ?_⟩
    simpa only [f, Function.comp_def, e.left_inv hxs] using hx
  obtain ⟨U, hUsub, hU, haU⟩ := mem_nhds_iff.mp hlocal
  refine ⟨F, hF, e, a, U, hU, haU, fun x hx => (hUsub hx).1, hpa, hes, heis, ?_⟩
  intro x hx v w
  change Real.exp (-2 * F (e x)) * g.pullbackCoefficients e x v w = _
  rw [hmetric x (hUsub hx).1, (hUsub hx).2]
  have hexp : Real.exp (-2 * (Real.log (lambda x) / 2)) * lambda x = 1 := by
    rw [show -2 * (Real.log (lambda x) / 2) = -Real.log (lambda x) by ring,
      Real.exp_neg, Real.exp_log (hlpos x (hUsub hx).1)]
    exact inv_mul_cancel₀ (hlpos x (hUsub hx).1).ne'
  rw [← mul_assoc, hexp, one_mul]

end PoincareConjecture.M60

end
