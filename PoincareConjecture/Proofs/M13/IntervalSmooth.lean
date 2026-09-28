import PoincareConjecture.Definitions.M11TimeInterval
import PoincareConjecture.Proofs.M13.WithinInverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M13

noncomputable def intervalChartExtension {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (p : D.Point) : ℝ → EuclideanSpace ℝ (Fin 1) :=
  Function.extend (Subtype.val : D.Point → ℝ) (extChartAt (𝓡∂ 1) p) 0

theorem intervalChartExtension_val {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (p x : D.Point) :
    intervalChartExtension D p (x : ℝ) = extChartAt (𝓡∂ 1) p x :=
  Subtype.val_injective.extend_apply _ _ _

theorem intervalChartExtension_contDiffOn {I : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (p : D.Point) :
    ContDiffOn ℝ ∞ (intervalChartExtension D p)
      ((Subtype.val : D.Point → ℝ) '' (extChartAt (𝓡∂ 1) p).source) := by
  let : ChartedSpace (EuclideanHalfSpace 1) D.Point := D.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ D.Point := D.isManifold
  let e := extChartAt (𝓡∂ 1) p
  let f : EuclideanSpace ℝ (Fin 1) → ℝ := fun y ↦ (e.symm y : ℝ)
  have hf : ContDiffOn ℝ ∞ f e.target :=
    (D.inclusion_smooth.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)).contDiffOn
  have hg : ContinuousOn (intervalChartExtension D p)
      ((Subtype.val : D.Point → ℝ) '' e.source) := by
    apply Topology.IsInducing.continuousOn_image_iff
      (Topology.IsEmbedding.subtypeVal.isInducing) |>.mpr
    simpa only [Function.comp_def, intervalChartExtension_val] using
      (continuousOn_extChartAt (I := 𝓡∂ 1) p)
  apply contDiffOn_leftInverse hf (uniqueDiffOn_extChartAt_target p) hg
  · rintro _ ⟨x, hx, rfl⟩
    rw [intervalChartExtension_val]
    exact e.map_source hx
  · rintro _ ⟨x, hx, rfl⟩
    rw [intervalChartExtension_val]
    change (e.symm (e x) : ℝ) = (x : ℝ)
    rw [e.left_inv hx]
  · rintro _ ⟨x, hx, rfl⟩
    rw [intervalChartExtension_val]
    have hy : e x ∈ e.target := e.map_source hx
    have hu := (uniqueDiffOn_extChartAt_target p (e x) hy).uniqueMDiffWithinAt
    have hi : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ)
        (Subtype.val : D.Point → ℝ) (e.symm (e x)) :=
      D.inclusion_smooth.mdifferentiable (by simp) _
    have he := (mdifferentiableWithinAt_extChartAt_symm hy).mono
      (extChartAt_target_subset_range p)
    have hcomp := mfderiv_comp_mfderivWithin (e x) hi he hu
    rw [mfderivWithin_eq_fderivWithin] at hcomp
    change fderivWithin ℝ f e.target (e x) = _ at hcomp
    change (fderivWithin ℝ f e.target (e x)).IsInvertible
    rw [hcomp, ← D.inclusionDerivative_eq]
    apply ContinuousLinearMap.IsInvertible.comp
    · exact ⟨D.inclusionDerivative _, rfl⟩
    · have hmono := (mdifferentiableWithinAt_extChartAt_symm hy).mfderivWithin_mono
        hu (extChartAt_target_subset_range p)
      rw [hmono]
      exact isInvertible_mfderivWithin_extChartAt_symm hy

theorem interval_map_smooth {I J : SpacetimeInterval}
    (D : SmoothSpacetimeInterval I) (E : SmoothSpacetimeInterval J)
    (f : D.Point → E.Point)
    (hf : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun x ↦ (f x : ℝ))) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ f := by
  have hc : Continuous f :=
    Topology.IsEmbedding.subtypeVal.continuous_iff.mpr hf.continuous
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨hc.continuousAt, ?_⟩
  let e := extChartAt (𝓡∂ 1) (f x)
  have hU : f ⁻¹' e.source ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (f x))
  have hcomp : ContMDiffOn (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      (fun y ↦ intervalChartExtension E (f x) (f y : ℝ)) (f ⁻¹' e.source) :=
    (intervalChartExtension_contDiffOn E (f x)).contMDiffOn.comp hf.contMDiffOn
      (fun y hy ↦ ⟨f y, hy, rfl⟩)
  have hpoint := (hcomp x (mem_extChartAt_source (f x))).contMDiffAt hU
  simpa only [Function.comp_def, intervalChartExtension_val] using hpoint

end PoincareConjecture.M13
