import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.RadialAxisMetric
import PoincareLib.Geometry.Riemannian.MetricComparison
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Intrinsic radial arclength and completeness

Morgan-Tian, Section 12.6, pp. 307-309, parametrizes a complete rotational
metric by radial arclength. The axis coefficients here come from the actual
metric. Its radial integral is strictly increasing. Completeness forces
the parameter to have unbounded positive range: otherwise the entire
Euclidean axis ray would lie in a compact Riemannian ball.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single 2 1

/-- Section 12.6, pp. 307-309: the actual radial coefficient is smooth
even at the tip, since it is the restriction of a smooth metric component. -/
theorem axisRadialCoefficient_contDiff (g : RiemannianMetric 3 StandardCapSpace) :
    ContDiff ℝ ∞ (axisRadialCoefficient g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  exact (((g.contDiffAt_euclideanCoefficients (r • e2)).comp r
    (contDiffAt_id.smul contDiffAt_const)).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const

/-- Section 12.6, pp. 307-309: the actual angular coefficient is smooth
in the original radial parameter, including at the tip. -/
theorem axisAngularCoefficient_contDiff (g : RiemannianMetric 3 StandardCapSpace) :
    ContDiff ℝ ∞ (axisAngularCoefficient g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  exact (((g.contDiffAt_euclideanCoefficients (r • e2)).comp r
    (contDiffAt_id.smul contDiffAt_const)).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const

/-- Section 12.6, pp. 307-309: intrinsic length from the tip along the axis. -/
noncomputable def radialArclength
    (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r, Real.sqrt (axisRadialCoefficient g s)

private theorem radialSpeed_continuous (g : RiemannianMetric 3 StandardCapSpace) :
    Continuous (fun r => Real.sqrt (axisRadialCoefficient g r)) :=
  (axisRadialCoefficient_contDiff g).continuous.sqrt

/-- Section 12.6, pp. 307-309: the radial arclength derivative is the
positive square root of the actual radial metric coefficient. -/
theorem radialArclength_hasDerivAt (g : RiemannianMetric 3 StandardCapSpace) (r : ℝ) :
    HasDerivAt (radialArclength g) (Real.sqrt (axisRadialCoefficient g r)) r :=
  intervalIntegral.integral_hasDerivAt_right
    ((radialSpeed_continuous g).intervalIntegrable 0 r)
    (radialSpeed_continuous g).aestronglyMeasurable.stronglyMeasurableAtFilter
    (radialSpeed_continuous g).continuousAt

/-- Section 12.6, pp. 307-309: radial arclength is a valid increasing
radial coordinate; no quotient or additional gauge data is involved. -/
theorem radialArclength_strictMono (g : RiemannianMetric 3 StandardCapSpace) :
    StrictMono (radialArclength g) :=
  strictMono_of_hasDerivAt_pos (radialArclength_hasDerivAt g)
    (fun r => Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r))

/-- Section 12.6, pp. 307-309: the intrinsic radial parameter vanishes at the tip. -/
theorem radialArclength_zero (g : RiemannianMetric 3 StandardCapSpace) :
    radialArclength g 0 = 0 := by simp [radialArclength]

/-- Section 12.6, pp. 307-309: the actual axis curve has precisely the
length used in the radial coordinate. This does not require completeness. -/
theorem pathELength_axis_eq_radialArclength
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 ≤ r) :
    g.pathELength (fun s : ℝ => s • e2) 0 r =
      ENNReal.ofReal (radialArclength g r) := by
  rw [g.pathELength_eq_lintegral_tangentNorm]
  have hd (s : ℝ) :
      mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) (fun t : ℝ => t • e2) s 1 = e2 := by
    rw [mfderiv_eq_fderiv]
    have hh : HasDerivAt (fun t : ℝ => t • e2) e2 s := by
      simpa using (hasDerivAt_id s).smul_const e2
    rw [hh.hasFDerivAt.fderiv]
    exact one_smul ℝ e2
  simp_rw [hd]
  change (∫⁻ s in Icc 0 r, ENNReal.ofReal (Real.sqrt (axisRadialCoefficient g s))) = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((radialSpeed_continuous g).continuousOn.integrableOn_Icc)
    (ae_of_all _ (fun s => Real.sqrt_nonneg _))]
  congr 1
  rw [radialArclength, intervalIntegral.integral_of_le hr,
    integral_Icc_eq_integral_Ioc]

/-- Section 12.6, pp. 307-309: axis length bounds the actual Riemannian
distance from the tip, before establishing the reverse radial bound. -/
theorem edist_axis_le_radialArclength
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 ≤ r) :
    g.edist 0 (r • e2) ≤ ENNReal.ofReal (radialArclength g r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← pathELength_axis_eq_radialArclength g hr]
  have hsm : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) 1 (fun s : ℝ => s • e2) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const)
  exact Manifold.riemannianEDist_le_pathELength hsm.contMDiffOn (by simp) rfl hr

/-- Section 12.6, pp. 307-309: completeness forces infinite radial
arclength. Compact metric balls cannot contain the whole Euclidean axis ray. -/
theorem radialArclength_unbounded
    (g : RiemannianMetric 3 StandardCapSpace) (hcomplete : MetricComplete g) (R : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ R < radialArclength g r := by
  by_contra! hbound
  have hR : 0 ≤ R := by simpa only [radialArclength_zero] using hbound 0 le_rfl
  have hcompact := Proofs.M09.isCompact_closure_metric_ball g hcomplete 0 (R + 1)
  obtain ⟨B, hBpos, hB⟩ := hcompact.isBounded.exists_pos_norm_le
  have hmem : (B + 1) • e2 ∈ g.ball 0 (R + 1) := by
    change g.edist 0 ((B + 1) • e2) < ENNReal.ofReal (R + 1)
    apply (edist_axis_le_radialArclength g (by linarith : 0 ≤ B + 1)).trans_lt
    apply ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < R + 1) |>.mpr
    linarith [hbound (B + 1) (by linarith : 0 ≤ B + 1)]
  have hh := hB ((B + 1) • e2) (subset_closure hmem)
  have hnorm : ‖(B + 1) • e2‖ = B + 1 := by
    simp [e2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ B + 1)]
  rw [hnorm] at hh
  linarith

/-- Section 12.6, pp. 307-309: every nonnegative intrinsic radius is
attained by the actual radial coordinate of a complete metric. -/
theorem exists_radialArclength_eq
    (g : RiemannianMetric 3 StandardCapSpace) (hcomplete : MetricComplete g)
    {s : ℝ} (hs : 0 ≤ s) :
    ∃ r : ℝ, 0 ≤ r ∧ radialArclength g r = s := by
  obtain ⟨R, hR, hRs⟩ := radialArclength_unbounded g hcomplete s
  have hc : Continuous (radialArclength g) :=
    continuous_iff_continuousAt.mpr (fun r => (radialArclength_hasDerivAt g r).continuousAt)
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc hR hc.continuousOn
    (show s ∈ Icc (radialArclength g 0) (radialArclength g R) from
      ⟨by simpa only [radialArclength_zero] using hs, hRs.le⟩)
  exact ⟨r, hr.1, heq⟩

end PoincareMT.M35.Uniqueness
