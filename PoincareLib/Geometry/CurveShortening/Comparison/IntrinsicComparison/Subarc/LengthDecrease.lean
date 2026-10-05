import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Boundary.Arithmetic
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Boundary.Geometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Length decrease for a proper boundary subarc

The actual metric length of a circle subarc splits exactly into its three
ordered pieces.  Removing either nondegenerate end piece therefore strictly
decreases the length.  This is the literal circle-subarc bookkeeping used in
Morgan--Tian, Lemma 19.46, Case (ii), pp. 477-478; see
`proof-work/tasks/M64/derivations/2026-09-25-nested-return-subarc.md`.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareMT

/-- Every nondegenerate parameter interval on a nonzero-radius boundary circle has positive
actual metric length. Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-nested-return-subarc.md. -/
theorem m64Intrinsic_boundaryLength_pos
    (N : IntrinsicAnnulus) {radius a b : ℝ} (hradius : radius ≠ 0) (hab : a < b) :
    0 < intrinsicBoundaryLength N.metric radius a b := by
  let f := intrinsicBoundarySpeed N.metric radius
  let F : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, f x
  have hf : Continuous f := (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous
  have hFderiv (t : ℝ) : HasDerivAt F (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hFmono : StrictMono F := strictMono_of_deriv_pos fun t => by
    rw [(hFderiv t).deriv]
    exact m64Intrinsic_boundarySpeed_pos N hradius t
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
  change F a + intrinsicBoundaryLength N.metric radius a b = F b at hadd
  linarith [hFmono hab]

/-- The actual length of an ordered boundary arc is the sum of the lengths of its left
omitted piece, retained subarc, and right omitted piece. Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-nested-return-subarc.md. -/
theorem m64Intrinsic_boundaryLength_subarc_decomposition
    (N : IntrinsicAnnulus) {radius a b c d : ℝ} (hradius : radius ≠ 0) :
    intrinsicBoundaryLength N.metric radius a b =
      intrinsicBoundaryLength N.metric radius a c +
        intrinsicBoundaryLength N.metric radius c d +
        intrinsicBoundaryLength N.metric radius d b := by
  have hf : Continuous (intrinsicBoundarySpeed N.metric radius) :=
    (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous
  have hacd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a c) (hf.intervalIntegrable c d)
  have hadb := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable a d) (hf.intervalIntegrable d b)
  unfold intrinsicBoundaryLength
  linarith

/-- The retained subarc is bounded by the parent length minus either actual omitted end
length. Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-nested-return-subarc.md. -/
theorem m64Intrinsic_boundaryLength_subarc_quantitative
    (N : IntrinsicAnnulus) {radius a b c d : ℝ} (hradius : radius ≠ 0)
    (hac : a ≤ c) (_hcd : c ≤ d) (hdb : d ≤ b) :
    intrinsicBoundaryLength N.metric radius c d ≤
        intrinsicBoundaryLength N.metric radius a b -
          intrinsicBoundaryLength N.metric radius a c ∧
      intrinsicBoundaryLength N.metric radius c d ≤
        intrinsicBoundaryLength N.metric radius a b -
          intrinsicBoundaryLength N.metric radius d b := by
  have hsplit :=
    m64Intrinsic_boundaryLength_subarc_decomposition N (radius := radius)
      (a := a) (b := b) (c := c) (d := d) hradius
  have hleft := m64Intrinsic_boundaryLength_nonneg N radius a c hac
  have hright := m64Intrinsic_boundaryLength_nonneg N radius d b hdb
  constructor <;> linarith

/-- A proper ordered boundary subarc has strictly smaller actual length than its parent arc.
Source/construction: proof-work/tasks/M64/derivations/2026-09-25-nested-return-subarc.md. -/
theorem m64Intrinsic_boundaryLength_proper_subarc_lt
    (N : IntrinsicAnnulus) {radius a b c d : ℝ} (hradius : radius ≠ 0)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hproper : a < c ∨ d < b) :
    intrinsicBoundaryLength N.metric radius c d <
      intrinsicBoundaryLength N.metric radius a b := by
  have hquant :=
    m64Intrinsic_boundaryLength_subarc_quantitative N hradius hac hcd hdb
  rcases hproper with hleft | hright
  · have hpos := m64Intrinsic_boundaryLength_pos N hradius hleft
    exact hquant.1.trans_lt (sub_lt_self _ hpos)
  · have hpos := m64Intrinsic_boundaryLength_pos N hradius hright
    exact hquant.2.trans_lt (sub_lt_self _ hpos)

end PoincareMT
