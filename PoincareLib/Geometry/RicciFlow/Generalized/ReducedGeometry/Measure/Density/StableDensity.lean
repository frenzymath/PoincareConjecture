import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StableLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# A measurable density on the actual stable image

The fixed-slice smooth reduced length gives the specified density
on the stable image. Its zero extension is globally measurable,
without imposing regularity on the raw infimum elsewhere.
Morgan-Tian Definition 6.70 and Lemma 6.71, pp. 140-141.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

/-- The actual reduced-volume density on the stable image, extended
by zero away from that image, Definition 6.70, p. 140. -/
noncomputable def stableReducedVolumeDensity (H : M14StableSet G T τ x E) :
    (G.slices (T - τ)).Point → ℝ :=
  (H.endpoint_slice_map '' H.carrier).indicator (fun q =>
    Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-M14ReducedLengthValue G T 0 τ x q.val))

/-- On the actual stable image the chosen density is precisely the
frozen reduced-volume integrand, Definition 6.70, p. 140. -/
theorem stableReducedVolumeDensity_eq (H : M14StableSet G T τ x E)
    {q : (G.slices (T - τ)).Point} (hq : q ∈ H.endpoint_slice_map '' H.carrier) :
    stableReducedVolumeDensity H q = Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G T 0 τ x q.val) :=
  indicator_of_mem hq _

/-- The actual density is continuous on the full stable image,
including at a physical terminal time, Lemma 6.71, p. 141. -/
theorem stableReducedVolumeDensity_continuousOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) :
    ContinuousOn (stableReducedVolumeDensity H) (H.endpoint_slice_map '' H.carrier) := by
  have hl := (reducedLengthValue_contMDiffOn_stableImage hM04 hM12 H).continuousOn
  exact (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn hl.neg)).congr
    (fun _ hq => stableReducedVolumeDensity_eq H hq)

/-- The zero extension of the actual stable density is globally
measurable, as required by calibrated transport in Lemma 6.71, p. 141. -/
theorem stableReducedVolumeDensity_measurable
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) : Measurable (stableReducedVolumeDensity H) := by
  classical
  have hl := (reducedLengthValue_contMDiffOn_stableImage hM04 hM12 H).continuousOn
  have hd := (continuousOn_const (c := Real.rpow τ (-(n : ℝ) / 2))).mul
    (Real.continuous_exp.comp_continuousOn hl.neg)
  exact hd.measurable_piecewise continuousOn_const (stableSliceChart H).open_target.measurableSet

/-- The chosen stable density is nonnegative everywhere, including
its zero extension, Definition 6.70, p. 140. -/
theorem stableReducedVolumeDensity_nonneg (H : M14StableSet G T τ x E)
    (q : (G.slices (T - τ)).Point) : 0 ≤ stableReducedVolumeDensity H q := by
  exact indicator_nonneg (fun _ _ =>
    (mul_pos (Real.rpow_pos_of_pos H.tau_pos _) (Real.exp_pos _)).le) q

end PoincareMT.M14
