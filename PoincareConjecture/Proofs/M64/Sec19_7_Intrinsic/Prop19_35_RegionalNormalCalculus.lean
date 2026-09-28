import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcLengthDecrease
import Mathlib.Analysis.Calculus.FDeriv.WithLp

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix intervalIntegral

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_boundary_prefix_length
    (N : IntrinsicAnnulus) {radius a b r : ℝ} (hradius : radius ≠ 0)
    (hab : a < b) (hr : 0 < r)
    (hlength : r < intrinsicBoundaryLength N.metric radius a b) :
    ∃ c ∈ Ioo a b, intrinsicBoundaryLength N.metric radius a c = r := by
  let f := intrinsicBoundarySpeed N.metric radius
  let F : ℝ → ℝ := fun t => ∫ x in a..t, f x
  have hf : Continuous f := (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous
  have hFderiv (t : ℝ) : HasDerivAt F (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hFderiv t).continuousAt)
  have hFmono : StrictMono F := strictMono_of_deriv_pos fun t => by
    rw [(hFderiv t).deriv]
    exact m64Intrinsic_boundarySpeed_pos N hradius t
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hFb : F b = intrinsicBoundaryLength N.metric radius a b := rfl
  obtain ⟨c, _, hc⟩ : ∃ c ∈ Icc a b, F c = r := by
    apply intermediate_value_Icc hab.le hFcont.continuousOn
    constructor
    · simpa only [hFa] using hr.le
    · simpa only [hFb] using hlength.le
  refine ⟨c, ⟨?_, ?_⟩, hc⟩
  · apply hFmono.lt_iff_lt.mp
    simpa only [hFa, hc] using hr
  · apply hFmono.lt_iff_lt.mp
    simpa only [hFb, hc] using hlength

theorem m64Intrinsic_normal_map_injective_of_metric_lower
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {x : AnnulusCoordinates}
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 +
        (v 1) ^ 2) ≤
      N.metric.inner (e x) (fderiv ℝ e x v) (fderiv ℝ e x v)) :
    Function.Injective (fderiv ℝ e x) := by
  refine (injective_iff_map_eq_zero (fderiv ℝ e x)).mpr ?_
  intro v hv
  have h := hbound v
  rw [hv, map_zero] at h
  have hsum : intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 +
      (v 1) ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hc)).mp
      (by simpa only [mul_zero] using h)
  have hv1 : v 1 = 0 := by
    nlinarith [mul_nonneg (sq_nonneg (intrinsicBoundarySpeed N.metric 1 (x 0)))
      (sq_nonneg (v 0))]
  have hspeed : 0 < intrinsicBoundarySpeed N.metric 1 (x 0) :=
    m64Intrinsic_boundarySpeed_pos N one_ne_zero (x 0)
  have hv0 : v 0 = 0 := by
    have hprod : intrinsicBoundarySpeed N.metric 1 (x 0) ^ 2 * (v 0) ^ 2 ≤ 0 := by
      nlinarith
    have hsq : (v 0) ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ (sq_pos_of_pos hspeed)).mp
        (by simpa only [mul_zero] using hprod)
    nlinarith [sq_nonneg (v 0)]
  ext i
  fin_cases i
  · exact hv0
  · exact hv1

theorem m64Intrinsic_coordinate_normal_ray_deriv
    {e : AnnulusCoordinates → AnnulusCoordinates} {a t : ℝ}
    (he : DifferentiableAt ℝ e !₂[a, t]) :
    deriv (fun s => e !₂[a, s]) t =
      fderiv ℝ e !₂[a, t] !₂[0, 1] := by
  let q : ℝ → AnnulusCoordinates := fun s => !₂[a, 0] + s • !₂[0, 1]
  have hq : q = fun s => !₂[a, s] := by
    funext s
    ext i
    fin_cases i <;> simp [q]
  have hline : HasDerivAt q (!₂[0, 1] : AnnulusCoordinates) t := by
    simpa only [q, id_eq, one_smul] using!
      ((hasDerivAt_id t).smul_const (!₂[0, 1] : AnnulusCoordinates)).const_add !₂[a, 0]
  rw [hq] at hline
  exact (he.hasFDerivAt.comp_hasDerivAt t hline).deriv

end PoincareConjecture
