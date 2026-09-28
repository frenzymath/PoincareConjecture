import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AreaLoss














noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture





theorem m64Intrinsic_retained_short_base_length_lower
    (N : IntrinsicAnnulus) {alpha R : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEsub : E ⊆ Icc (0 : ℝ) rampPeriod)
    {height : ℝ → ℝ} (hh : Measurable height) :
    let X := Ico (0 : ℝ) rampPeriod ∩
      {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}
    let S := X \ E
    intrinsicBoundaryLength N.metric 1 0 rampPeriod -
        m64IntrinsicHighCurvatureLength N alpha -
        (∫ s in E, intrinsicBoundarySpeed N.metric 1 s) -
        m64IntrinsicLongFiberLength N S height R ≤
      ∫ s in S ∩ {s | height s < R}, intrinsicBoundarySpeed N.metric 1 s := by
  let speed := intrinsicBoundarySpeed N.metric 1
  let B := Ico (0 : ℝ) rampPeriod
  let Y := {s | alpha < intrinsicGeodesicCurvature N.metric N.connection 1 s}
  let X := B ∩ {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}
  let S := X \ E
  have hspeed : Continuous speed :=
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hY : MeasurableSet Y := (isOpen_lt continuous_const
    (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0))).measurableSet
  have hXB : X ⊆ B := inter_subset_left
  have hBI : B ⊆ Icc (0 : ℝ) rampPeriod := Ico_subset_Icc_self
  have hXeq : B \ Y = X := by
    ext s
    simp only [Y, X, Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_lt]
  have hhigh : (∫ s in B ∩ Y, speed s) = m64IntrinsicHighCurvatureLength N alpha := by
    apply setIntegral_congr_set
    exact Ico_ae_eq_Ioc.inter (ae_eq_refl Y)
  have hfull : (∫ s in B, speed s) = intrinsicBoundaryLength N.metric 1 0 rampPeriod := by
    change (∫ s in Ico (0 : ℝ) rampPeriod, speed s) = ∫ s in (0 : ℝ)..rampPeriod, speed s
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ rampPeriod from Real.two_pi_pos.le)]
    exact setIntegral_congr_set Ico_ae_eq_Ioc
  have hsplitX := integral_inter_add_sdiff (μ := volume) (s := B) hY
    (hspeed.integrableOn_Icc.mono_set hBI)
  rw [hXeq, hhigh, hfull] at hsplitX
  have hsplitS := integral_inter_add_sdiff (μ := volume) (s := X) hE
    (hspeed.integrableOn_Icc.mono_set (hXB.trans hBI))
  have hremove : (∫ s in X ∩ E, speed s) ≤ ∫ s in E, speed s := by
    apply setIntegral_mono_set (hspeed.integrableOn_Icc.mono_set hEsub)
      (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
    exact Eventually.of_forall (fun _ hs => hs.2)
  have hlong : MeasurableSet {s | R ≤ height s} := measurableSet_le measurable_const hh
  have hsplitZ := integral_inter_add_sdiff (μ := volume) (s := S) hlong
    (hspeed.integrableOn_Icc.mono_set (sdiff_subset.trans (hXB.trans hBI)))
  have hZeq : S \ {s | R ≤ height s} = S ∩ {s | height s < R} := by
    ext s
    simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_le]
  change (∫ s in S ∩ {s | R ≤ height s}, speed s) +
    (∫ s in S \ {s | R ≤ height s}, speed s) = ∫ s in S, speed s at hsplitZ
  rw [hZeq] at hsplitZ
  change m64IntrinsicLongFiberLength N S height R +
    (∫ s in S ∩ {s | height s < R}, speed s) = ∫ s in S, speed s at hsplitZ
  change intrinsicBoundaryLength N.metric 1 0 rampPeriod -
      m64IntrinsicHighCurvatureLength N alpha - (∫ s in E, speed s) -
      m64IntrinsicLongFiberLength N S height R ≤
    ∫ s in S ∩ {s | height s < R}, speed s
  linarith




theorem m64Intrinsic_retained_short_base_stretched_length_gt
    (N : IntrinsicAnnulus) {delta r alpha R : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / r ≤ alpha)
    {E : Set ℝ} (hE : MeasurableSet E) (hEsub : E ⊆ Icc (0 : ℝ) rampPeriod)
    {height : ℝ → ℝ} (hh : Measurable height)
    (hfocus : (∫ s in E, intrinsicBoundarySpeed N.metric 1 s) <
      3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50)
    (harea : m64IntrinsicLongFiberLength N
        ((Ico (0 : ℝ) rampPeriod ∩
          {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}) \ E) height R <
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 10) :
    (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod <
      (1 - delta) *
        ∫ s in ((Ico (0 : ℝ) rampPeriod ∩
          {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}) \ E) ∩
            {s | height s < R}, intrinsicBoundarySpeed N.metric 1 s := by
  have hcurvature := m64Intrinsic_high_curvature_length_lt N hdelta hr hfirst hturn halpha
  have hremaining := m64Intrinsic_retained_short_base_length_lower N hE hEsub hh
    (alpha := alpha) (R := R)
  dsimp only at hremaining
  let L := intrinsicBoundaryLength N.metric 1 0 rampPeriod
  let Z := ((Ico (0 : ℝ) rampPeriod ∩
    {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}) \ E) ∩
      {s | height s < R}
  have hL : 0 < L := hr.trans hfirst
  have hZ : (41 / 50 : ℝ) * L < ∫ s in Z, intrinsicBoundarySpeed N.metric 1 s := by
    dsimp only [L, Z]
    linarith
  have hpositive : 0 < 1 - delta := by linarith
  have hscale := mul_lt_mul_of_pos_left hZ hpositive
  have hcoefficient : (3 / 4 : ℝ) < (1 - delta) * (41 / 50) := by linarith
  have hscaled := mul_lt_mul_of_pos_right hcoefficient hL
  change (3 / 4 : ℝ) * L < (1 - delta) * ∫ s in Z, intrinsicBoundarySpeed N.metric 1 s
  nlinarith only [hscale, hscaled]

end PoincareConjecture
