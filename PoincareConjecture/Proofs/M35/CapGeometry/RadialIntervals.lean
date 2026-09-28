import PoincareConjecture.Proofs.M35.Uniqueness.RadialArclength

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single 2 1

theorem pathELength_axis_segment_eq
    (g : RiemannianMetric 3 StandardCapSpace) {a b : ℝ} (hab : a ≤ b) :
    g.pathELength (fun s : ℝ => s • e2) a b =
      ENNReal.ofReal (radialArclength g b - radialArclength g a) := by
  rw [g.pathELength_eq_lintegral_tangentNorm]
  have hd (s : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t : ℝ => t • e2) s 1 = e2 := by
    rw [mfderiv_eq_fderiv]
    have hh : HasDerivAt (fun t : ℝ => t • e2) e2 s := by
      simpa using (hasDerivAt_id s).smul_const e2
    rw [hh.hasFDerivAt.fderiv]
    exact one_smul ℝ e2
  simp_rw [hd]
  change (∫⁻ s in Icc a b, ENNReal.ofReal (Real.sqrt (axisRadialCoefficient g s))) = _
  have hcont : Continuous (fun s => Real.sqrt (axisRadialCoefficient g s)) :=
    (axisRadialCoefficient_contDiff g).continuous.sqrt
  rw [← ofReal_integral_eq_lintegral_ofReal hcont.continuousOn.integrableOn_Icc
    (ae_of_all _ (fun s => Real.sqrt_nonneg _))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => radialArclength_hasDerivAt g s) (hcont.intervalIntegrable a b)

theorem edist_axis_segment_le
    (g : RiemannianMetric 3 StandardCapSpace) {a b : ℝ} (hab : a ≤ b) :
    g.edist (a • e2) (b • e2) ≤
      ENNReal.ofReal (radialArclength g b - radialArclength g a) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← pathELength_axis_segment_eq g hab]
  have hsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun s : ℝ => s • e2) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const)
  exact Manifold.riemannianEDist_le_pathELength hsm.contMDiffOn rfl rfl hab

theorem exists_outward_radial_interval
    (g : RiemannianMetric 3 StandardCapSpace) (hcomplete : MetricComplete g)
    {a L : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    ∃ b : ℝ, a < b ∧ radialArclength g b - radialArclength g a = L := by
  have hsa : 0 ≤ radialArclength g a := by
    simpa only [radialArclength_zero] using (radialArclength_strictMono g).monotone ha
  obtain ⟨b, _hb, heq⟩ := exists_radialArclength_eq g hcomplete (add_nonneg hsa hL.le)
  refine ⟨b, ?_, by linarith⟩
  apply (radialArclength_strictMono g).lt_iff_lt.mp
  rw [heq]
  linarith

theorem radial_interval_subset_ball
    (g : RiemannianMetric 3 StandardCapSpace) {a b L : ℝ}
    (hL : 0 < L) (hlength : radialArclength g b - radialArclength g a = L) :
    ∀ u ∈ Icc a b, u • e2 ∈ g.ball (a • e2) (2 * L) := by
  intro u hu
  change g.edist (a • e2) (u • e2) < ENNReal.ofReal (2 * L)
  apply (edist_axis_segment_le g hu.1).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) hL)).mpr
  have h := (radialArclength_strictMono g).monotone hu.2
  linarith

end PoincareConjecture.M35.Uniqueness
