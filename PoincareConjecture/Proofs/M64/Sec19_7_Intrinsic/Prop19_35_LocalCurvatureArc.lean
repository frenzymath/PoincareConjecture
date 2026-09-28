import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalCollisionSeparation





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped intervalIntegral

namespace PoincareConjecture





theorem m64Intrinsic_exists_local_curvature_arc
    (N : IntrinsicAnnulus) {a M L : ℝ}
    (hcurv : intrinsicGeodesicCurvature N.metric N.connection 1 a < M) (hL : 0 < L) :
    ∃ l u : ℝ, l < a ∧ a < u ∧ u - l < rampPeriod ∧
      intrinsicBoundaryLength N.metric 1 l u < L ∧
      ∀ p ∈ Icc l u, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ M := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, intrinsicBoundarySpeed N.metric 1 t
  have hs := (m64Intrinsic_contDiff_boundarySpeed N one_ne_zero).continuous
  have hF : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hs.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt)
  have hk := m64Intrinsic_continuous_geodesicCurvature N one_ne_zero
  let V : Set ℝ := {p | intrinsicGeodesicCurvature N.metric N.connection 1 p < M} ∩
    {p | |F p - F a| < L / 4} ∩ {p | |p - a| < rampPeriod / 4}
  have hV : IsOpen V :=
    ((isOpen_lt hk continuous_const).inter
      (isOpen_lt (hF.sub continuous_const).abs continuous_const)).inter
      (isOpen_lt (continuous_id.sub continuous_const).abs continuous_const)
  have haV : a ∈ V := by
    refine ⟨⟨hcurv, ?_⟩, ?_⟩
    · change |F a - F a| < L / 4
      simpa only [sub_self, abs_zero] using (by positivity : (0 : ℝ) < L / 4)
    · change |a - a| < rampPeriod / 4
      simpa only [sub_self, abs_zero] using
        (by exact div_pos Real.two_pi_pos (by norm_num) : (0 : ℝ) < rampPeriod / 4)
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hV a haV
  let l := a - d / 2
  let u := a + d / 2
  have hla : l < a := by dsimp only [l]; linarith only [hd]
  have hau : a < u := by dsimp only [u]; linarith only [hd]
  have hlu : l < u := hla.trans hau
  have hsub : Icc l u ⊆ V := by
    intro p hp
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp only [l, u] at hp
    constructor <;> linarith only [hp.1, hp.2, hd]
  have hl := hsub (show l ∈ Icc l u from ⟨le_rfl, hlu.le⟩)
  have hu := hsub (show u ∈ Icc l u from ⟨hlu.le, le_rfl⟩)
  refine ⟨l, u, hla, hau, ?_, ?_, fun p hp => (hsub hp).1.1.le⟩
  · have hleft := (abs_lt.mp (show |l - a| < rampPeriod / 4 from hl.2)).1
    have hright := (abs_lt.mp (show |u - a| < rampPeriod / 4 from hu.2)).2
    have hP : 0 < rampPeriod := Real.two_pi_pos
    linarith only [hleft, hright, hP]
  · have hleft := (abs_lt.mp (show |F l - F a| < L / 4 from hl.1.2)).1
    have hright := (abs_lt.mp (show |F u - F a| < L / 4 from hu.1.2)).2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hs.intervalIntegrable 0 l) (hs.intervalIntegrable l u)
    change F l + intrinsicBoundaryLength N.metric 1 l u = F u at hadd
    linarith only [hleft, hright, hadd, hL]

end PoincareConjecture
