import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Local smoothness of sphere-valued maps

The stereographic atlas detects smoothness by the sphere inclusion.
This local version of Mathlib's sphere codomain restriction lemma is
used for the polar inverse in Morgan-Tian Lemma 12.2, pp. 294-295.
See the M34 cylindrical-end derivation for its domain restrictions.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {m : WithTop ℕ∞} {f : M → sphere (0 : E) 1} {x : M}

/-- Smoothness of the included sphere-valued map implies smoothness at
the same point. This is a local statement and permits a nonsmooth total
extension elsewhere (Lemma 12.2 polar inverse, pp. 294-295). -/
theorem ContMDiffAt.of_coe_sphere
    (hf : ContMDiffAt I 𝓘(ℝ, E) m (fun y => (f y : E)) x) :
    ContMDiffAt I (𝓡 n) m f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousAt, ?_⟩
  let v := -(f x)
  let U : _ ≃ₗᵢ[ℝ] _ := (OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere v)).repr
  have hv : innerSL ℝ (v : E) (f x : E) ≠ 1 := by
    have hnorm : ‖(f x : E)‖ = 1 := norm_eq_of_mem_sphere (f x)
    simp only [v, coe_neg_sphere, innerSL_apply_apply, inner_neg_left,
      real_inner_self_eq_norm_sq, hnorm]
    norm_num
  have hs : ContDiffAt ℝ m (stereoToFun (v : E)) (f x : E) :=
    contDiffOn_stereoToFun.contDiffAt
      ((isOpen_ne.preimage (innerSL ℝ (v : E)).continuous).mem_nhds hv)
  have h := (U.contDiff.contDiffAt.comp (f x : E) hs).contMDiffAt.comp x hf
  convert! h using 1
