import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurvatureLoss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
















noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture




theorem m64Intrinsic_sum_disjoint_turning_le
    (N : IntrinsicAnnulus) (T : Finset (ℝ × ℝ))
    (hbounds : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ rampPeriod)
    (hdisj : (T : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2)) :
    (∑ p ∈ T, intrinsicGeodesicCurvatureIntegral
      N.metric N.connection 1 p.1 p.2) ≤
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod := by
  let density : ℝ → ℝ := fun s =>
    intrinsicGeodesicCurvature N.metric N.connection 1 s *
      intrinsicBoundarySpeed N.metric 1 s
  have hdensity : Continuous density :=
    m64Intrinsic_continuous_turning_density N (by norm_num : (1 : ℝ) ≠ 0)
  have hint : IntegrableOn density (Ioc (0 : ℝ) rampPeriod) :=
    hdensity.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hsub (p : ℝ × ℝ) (hp : p ∈ T) :
      Ioc p.1 p.2 ⊆ Ioc (0 : ℝ) rampPeriod := by
    intro s hs
    exact ⟨(hbounds p hp).1.trans_lt hs.1, hs.2.trans (hbounds p hp).2.2⟩
  have hdisj' : (T : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioc p.1 p.2) := by
    intro p hp q hq hpq
    exact Ioc_disjoint_Ioc.mpr (Ioo_disjoint_Ioo.mp (hdisj hp hq hpq))
  have hunion : (⋃ p ∈ T, Ioc p.1 p.2) ⊆ Ioc (0 : ℝ) rampPeriod := by
    intro s hs
    obtain ⟨p, hs⟩ := mem_iUnion.mp hs
    obtain ⟨hp, hs⟩ := mem_iUnion.mp hs
    exact hsub p hp hs
  have hsum := integral_biUnion_finset T
    (fun _ _ => measurableSet_Ioc) hdisj'
    (fun p hp => hint.mono_set (hsub p hp))
  have hmono : (∫ s in ⋃ p ∈ T, Ioc p.1 p.2, density s) ≤
      ∫ s in Ioc (0 : ℝ) rampPeriod, density s := by
    apply setIntegral_mono_set hint
    · exact Filter.Eventually.of_forall (fun s =>
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · exact Filter.Eventually.of_forall (fun s hs => hunion hs)
  rw [hsum] at hmono
  change (∑ p ∈ T, intrinsicGeodesicCurvatureIntegral
    N.metric N.connection 1 p.1 p.2) ≤ _
  calc
    _ = ∑ p ∈ T, ∫ s in Ioc p.1 p.2, density s := by
      apply Finset.sum_congr rfl
      intro p hp
      exact intervalIntegral.integral_of_le (hbounds p hp).2.1
    _ ≤ ∫ s in Ioc (0 : ℝ) rampPeriod, density s := hmono
    _ = intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod := by
      exact (intervalIntegral.integral_of_le Real.two_pi_pos.le).symm




theorem m64Intrinsic_sine_focusing_length_le_twice_radius_turning
    {R kappa L T : ℝ} (hR : 0 < R) (hkappa : 0 < kappa)
    (hangle : kappa * R ≤ Real.pi / 4) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hendpoint : Real.cos (kappa * R) * L ≤
      (Real.sin (kappa * R) / kappa) * T) :
    L ≤ 2 * R * T := by
  have hx : 0 ≤ kappa * R := (mul_pos hkappa hR).le
  have hcos : (1 / 2 : ℝ) ≤ Real.cos (kappa * R) := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hx
      (by nlinarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi) hangle
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := by
      simpa only [Real.sqrt_one] using
        Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
    rw [Real.cos_pi_div_four] at hmono
    linarith
  have hsin : Real.sin (kappa * R) / kappa ≤ R := by
    apply (div_le_iff₀ hkappa).mpr
    simpa only [mul_comm] using Real.sin_le hx
  have hleft := mul_le_mul_of_nonneg_right hcos hL
  have hright := mul_le_mul_of_nonneg_right hsin hT
  nlinarith only [hleft, hendpoint, hright]





theorem m64Intrinsic_focusing_interval_length_lt_three_fiftieths
    (N : IntrinsicAnnulus) {delta r R kappa : ℝ}
    (hdelta : 0 < delta) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r)
    (hR : 0 < R) (hkappa : 0 < kappa)
    (hangle : kappa * R ≤ Real.pi / 4)
    (hsmall : R ≤ 3 * r / (200 * delta))
    (T : Finset (ℝ × ℝ))
    (hbounds : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ rampPeriod)
    (hdisj : (T : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Ioo p.1 p.2))
    (hendpoint : ∀ p ∈ T,
      Real.cos (kappa * R) * intrinsicBoundaryLength N.metric 1 p.1 p.2 ≤
        (Real.sin (kappa * R) / kappa) *
          intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 p.1 p.2) :
    (∑ p ∈ T, intrinsicBoundaryLength N.metric 1 p.1 p.2) <
      3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 := by
  have hpoint : ∀ p ∈ T, intrinsicBoundaryLength N.metric 1 p.1 p.2 ≤
      2 * R * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 p.1 p.2 := by
    intro p hp
    exact m64Intrinsic_sine_focusing_length_le_twice_radius_turning hR hkappa hangle
      (m64Intrinsic_boundaryLength_nonneg N 1 p.1 p.2 (hbounds p hp).2.1)
      (m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 p.1 p.2 (hbounds p hp).2.1)
      (hendpoint p hp)
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at hsum
  have htotal := m64Intrinsic_sum_disjoint_turning_le N T hbounds hdisj
  have hturning := m64Intrinsic_total_turning_lt N hdelta hr hfirst hturn
  have hcoefficient : (2 * R) * (2 * delta / r) ≤ (3 / 50 : ℝ) := by
    have hscaled := (le_div_iff₀ (by positivity : 0 < 200 * delta)).mp hsmall
    calc
      (2 * R) * (2 * delta / r) = (4 * R * delta) / r := by ring
      _ ≤ 3 / 50 := (div_le_iff₀ hr).mpr (by nlinarith only [hscaled])
  have hL : 0 ≤ intrinsicBoundaryLength N.metric 1 0 rampPeriod := (hr.trans hfirst).le
  calc
    _ ≤ (2 * R) * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod :=
      hsum.trans (mul_le_mul_of_nonneg_left htotal (by positivity))
    _ < (2 * R) * ((2 * delta / r) *
        intrinsicBoundaryLength N.metric 1 0 rampPeriod) :=
      mul_lt_mul_of_pos_left hturning (by positivity)
    _ ≤ 3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 := by
      have h := mul_le_mul_of_nonneg_right hcoefficient hL
      nlinarith only [h]

end PoincareConjecture
