import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingCover
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TotalTurning
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral ENNReal

namespace PoincareConjecture

theorem m64Intrinsic_exists_weighted_focusing_cover
    {f g : ℝ → ℝ} (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hg : Continuous g) (hgnonneg : ∀ x, 0 ≤ g x)
    {P A τ : ℝ} (hP : 0 < P) (hA : 0 ≤ A) (hτ : 3 < τ)
    (T : Set (ℝ × ℝ))
    (hT : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ P)
    (hfocus : ∀ p ∈ T,
      (∫ x in p.1..p.2, f x) ≤ A * ∫ x in p.1..p.2, g x) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) P ∧
      (∀ p ∈ T, Icc p.1 p.2 ⊆ E) ∧
      (∫ x in E, f x) ≤ (τ * A) * ∫ x in (0 : ℝ)..P, g x := by
  let F : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, f x
  have hFd (t : ℝ) : HasDerivAt F (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hFc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hFd t).continuousAt)
  have hFm : StrictMono F := strictMono_of_deriv_pos
    (fun t => by rw [(hFd t).deriv]; exact hfpos t)
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  have hdiff (a b : ℝ) : F b - F a = ∫ x in a..b, f x := by
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 a) (hf.intervalIntegrable a b)
    change F a + (∫ x in a..b, f x) = F b at h
    linarith
  let ν := ((volume.withDensity (fun x => ENNReal.ofReal (g x))).restrict (Icc 0 P)).map F
  have hν (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ P) :
      ν (Icc (F a) (F b)) = ENNReal.ofReal (∫ x in a..b, g x) := by
    have hpre : F ⁻¹' Icc (F a) (F b) = Icc a b := by
      ext x
      simp only [mem_preimage, mem_Icc, hFm.le_iff_le]
    have hsub : Icc a b ⊆ Icc (0 : ℝ) P := Icc_subset_Icc ha hb
    change Measure.map F _ _ = _
    rw [Measure.map_apply hFc.measurable measurableSet_Icc, hpre,
      Measure.restrict_apply measurableSet_Icc, inter_eq_left.mpr hsub,
      withDensity_apply _ measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Icc
        (Eventually.of_forall hgnonneg), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
  have hνuniv : ν univ = ENNReal.ofReal (∫ x in (0 : ℝ)..P, g x) := by
    change Measure.map F _ _ = _
    rw [Measure.map_apply hFc.measurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter,
      withDensity_apply _ measurableSet_Icc,
      ← ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Icc
        (Eventually.of_forall hgnonneg), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hP.le]
  let Q := (fun p : ℝ × ℝ => (F p.1, F p.2)) '' T
  have hQ (q : ℝ × ℝ) (hq : q ∈ Q) :
      0 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ F P := by
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨ha, hab, hb⟩ := hT p hp
    exact ⟨by simpa only [hF0] using hFm.monotone ha, hFm hab, hFm.monotone hb⟩
  have hQfocus (q : ℝ × ℝ) (hq : q ∈ Q) :
      ENNReal.ofReal (q.2 - q.1) ≤ ENNReal.ofReal A * ν (Icc q.1 q.2) := by
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨ha, hab, hb⟩ := hT p hp
    rw [hν p.1 p.2 ha hab.le hb, ← ENNReal.ofReal_mul hA, hdiff]
    exact ENNReal.ofReal_le_ofReal (hfocus p hp)
  obtain ⟨B, hB, hcover, hbound⟩ :=
    m64Intrinsic_exists_measurable_interval_cover Q ν hτ hQ hQfocus
  let E := Icc (0 : ℝ) P ∩ F ⁻¹' B
  have hE : MeasurableSet E := measurableSet_Icc.inter (hFc.measurable hB)
  have hEsub : E ⊆ Icc (0 : ℝ) P := inter_subset_left
  have himage : F '' E ⊆ B := by rintro _ ⟨x, hx, rfl⟩; exact hx.2
  have hlength : volume (F '' E) = ∫⁻ x in E, ENNReal.ofReal (f x) := by
    simpa only [Pi.one_apply, lintegral_one, Measure.restrict_apply_univ,
      mul_one, abs_of_pos (hfpos _)] using
      lintegral_image_eq_lintegral_abs_deriv_mul hE
        (fun x _ => (hFd x).hasDerivWithinAt) hFm.injective.injOn (fun _ => 1)
  refine ⟨E, hE, hEsub, ?_, ?_⟩
  · intro p hp x hx
    obtain ⟨ha, _, hb⟩ := hT p hp
    exact ⟨Icc_subset_Icc ha hb hx,
      hcover _ (mem_image_of_mem _ hp) ⟨hFm.monotone hx.1, hFm.monotone hx.2⟩⟩
  · have hle := (measure_mono himage).trans hbound
    rw [hlength, hνuniv, ← ENNReal.ofReal_mul (by positivity : 0 ≤ τ * A),
      ← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc.mono_set hEsub)
        (Eventually.of_forall (fun x => (hfpos x).le))] at hle
    apply (ENNReal.ofReal_le_ofReal_iff ?_).mp hle
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg hP.le (fun x _ => hgnonneg x))

theorem m64Intrinsic_exists_boundary_focusing_cover
    (N : IntrinsicAnnulus) {A τ : ℝ} (hA : 0 ≤ A) (hτ : 3 < τ)
    (T : Set (ℝ × ℝ))
    (hT : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ rampPeriod)
    (hfocus : ∀ p ∈ T, intrinsicBoundaryLength N.metric 1 p.1 p.2 ≤
      A * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 p.1 p.2) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) rampPeriod ∧
      (∀ p ∈ T, Icc p.1 p.2 ⊆ E) ∧
      (∫ x in E, intrinsicBoundarySpeed N.metric 1 x) ≤
        (τ * A) * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod := by
  exact m64Intrinsic_exists_weighted_focusing_cover
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
    (m64Intrinsic_boundarySpeed_pos N (by norm_num : (1 : ℝ) ≠ 0))
    (m64Intrinsic_continuous_turning_density N (by norm_num : (1 : ℝ) ≠ 0))
    (fun _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    Real.two_pi_pos hA hτ T hT hfocus

end PoincareConjecture
