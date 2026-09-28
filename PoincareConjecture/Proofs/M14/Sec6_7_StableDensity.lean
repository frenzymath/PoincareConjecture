import PoincareConjecture.Proofs.M14.Sec6_7_StableLength
import PoincareConjecture.Definitions.M14MeasureTransport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}



noncomputable def stableReducedVolumeDensity (H : M14StableSet G T τ x E) :
    (G.slices (T - τ)).Point → ℝ :=
  (H.endpoint_slice_map '' H.carrier).indicator (fun q =>
    Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-M14ReducedLengthValue G T 0 τ x q.val))



theorem stableReducedVolumeDensity_eq (H : M14StableSet G T τ x E)
    {q : (G.slices (T - τ)).Point} (hq : q ∈ H.endpoint_slice_map '' H.carrier) :
    stableReducedVolumeDensity H q = Real.rpow τ (-(n : ℝ) / 2) *
      Real.exp (-M14ReducedLengthValue G T 0 τ x q.val) :=
  indicator_of_mem hq _



theorem stableReducedVolumeDensity_continuousOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) :
    ContinuousOn (stableReducedVolumeDensity H) (H.endpoint_slice_map '' H.carrier) := by
  have hl := (reducedLengthValue_contMDiffOn_stableImage hM04 hM12 H).continuousOn
  exact (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn hl.neg)).congr
    (fun _ hq => stableReducedVolumeDensity_eq H hq)



theorem stableReducedVolumeDensity_measurable
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) : Measurable (stableReducedVolumeDensity H) := by
  classical
  have hl := (reducedLengthValue_contMDiffOn_stableImage hM04 hM12 H).continuousOn
  have hd := (continuousOn_const (c := Real.rpow τ (-(n : ℝ) / 2))).mul
    (Real.continuous_exp.comp_continuousOn hl.neg)
  exact hd.measurable_piecewise continuousOn_const (stableSliceChart H).open_target.measurableSet



theorem stableReducedVolumeDensity_nonneg (H : M14StableSet G T τ x E)
    (q : (G.slices (T - τ)).Point) : 0 ≤ stableReducedVolumeDensity H q := by
  exact indicator_nonneg (fun _ _ =>
    (mul_pos (Real.rpow_pos_of_pos H.tau_pos _) (Real.exp_pos _)).le) q

end PoincareConjecture.M14
