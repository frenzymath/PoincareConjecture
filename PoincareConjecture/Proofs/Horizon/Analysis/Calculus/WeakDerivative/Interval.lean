import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Poincare.Analysis.WeakDerivative

private theorem exists_support_interval {K : Set ℝ} {l r : ℝ}
    (hK : IsCompact K) (hKr : K ⊆ Ioo l r) (hlr : l < r) :
    ∃ c d : ℝ, l < c ∧ c ≤ d ∧ d < r ∧ K ⊆ Ioo c d := by
  let K' := insert ((l + r) / 2) K
  have hc : IsCompact K' := hK.insert _
  have hn : K'.Nonempty := ⟨(l + r) / 2, by simp [K']⟩
  have hs : K' ⊆ Ioo l r := by
    intro x hx
    rcases hx with rfl | hx
    · constructor <;> linarith
    · exact hKr hx
  obtain ⟨a, ha⟩ := hc.exists_isLeast hn
  obtain ⟨b, hb⟩ := hc.exists_isGreatest hn
  obtain ⟨c, hlc, hca⟩ := exists_between (hs ha.1).1
  obtain ⟨d, hbd, hdr⟩ := exists_between (hs hb.1).2
  refine ⟨c, d, hlc, le_of_lt (hca.trans_le (ha.2 hb.1) |>.trans hbd), hdr, ?_⟩
  intro x hx
  exact ⟨hca.trans_le (ha.2 (mem_insert_of_mem _ hx)),
    (hb.2 (mem_insert_of_mem _ hx)).trans_lt hbd⟩

theorem exists_compactSupport_primitive {φ : ℝ → ℝ} {l r : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo l r) (hz : ∫ x, φ x = 0) (hlr : l < r) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo l r ∧ ∀ x, deriv η x = φ x := by
  obtain ⟨c, d, hlc, hcd, hdr, hsd⟩ := exists_support_interval hc.isCompact hs hlr
  let η : ℝ → ℝ := fun x => ∫ t in c..x, φ t
  have hder (x : ℝ) : HasDerivAt η (φ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hφ.continuous.intervalIntegrable c x)
      hφ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hφ.continuous.continuousAt
  have hη : ContDiff ℝ ∞ η := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hder x).differentiableAt, ?_⟩
    rw [show deriv η = φ by funext x; exact (hder x).deriv]
    exact hφ
  have hsupport : Function.support η ⊆ Icc c d := by
    intro x hx
    by_contra hx'
    have hne : η x ≠ 0 := hx
    have hout : x < c ∨ d < x := by simpa only [mem_Icc, not_and_or, not_le] using hx'
    rcases hout with hxc | hdx
    · apply hne
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      apply image_eq_zero_of_notMem_tsupport
      intro ht'
      have ht0 : t ≤ c := by
        rw [uIoc_of_ge hxc.le] at ht
        exact ht.2
      exact (not_lt_of_ge ht0) (hsd ht').1
    · apply hne
      change (∫ t in c..x, φ t) = 0
      rw [intervalIntegral.integral_eq_integral_of_support_subset, hz]
      exact fun t ht => ⟨(hsd (subset_tsupport φ ht)).1,
        (hsd (subset_tsupport φ ht)).2.le.trans hdx.le⟩
  have hts : tsupport η ⊆ Icc c d := closure_minimal hsupport isClosed_Icc
  refine ⟨η, hη, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport,
    hts.trans ?_, fun x => (hder x).deriv⟩
  exact fun x hx => ⟨hlc.trans_le hx.1, hx.2.trans_lt hdr⟩

private theorem exists_normalized_test {l r : ℝ} (hlr : l < r) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ioo l r ∧ (∫ x, ψ x) = 1 := by
  let b : ContDiffBump ((l + r) / 2) :=
    { rIn := (r - l) / 8
      rOut := (r - l) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, ?_, b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro x hx
  have hx' := Metric.mem_closedBall.mp hx
  rw [Real.dist_eq] at hx'
  have hh := abs_le.mp hx'
  dsimp [b] at hh
  constructor <;> linarith

private theorem integrable_mul_test {C φ : ℝ → ℝ} {l r : ℝ}
    (hC : ContinuousOn C (Ioo l r)) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioo l r) :
    Integrable (fun x => φ x * C x) := by
  apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
  exact (hφ.continuousOn.mul hC).continuous_of_tsupport_subset isOpen_Ioo
    (tsupport_mul_subset_left.trans hs)

theorem eqOn_const_of_integral_deriv_mul_eq_zero {C : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hC : ContinuousOn C (Ioo l r))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo l r → (∫ x, deriv η x * C x) = 0) :
    ∃ c : ℝ, EqOn C (fun _ => c) (Ioo l r) := by
  obtain ⟨ψ, hψ, hψc, hψs, hψi⟩ := exists_normalized_test hlr
  let c : ℝ := ∫ x, ψ x * C x
  have htest (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφs : tsupport φ ⊆ Ioo l r) : (∫ x, φ x * (C x - c)) = 0 := by
    let q : ℝ → ℝ := fun x => φ x - (∫ t, φ t) * ψ x
    have hq : ContDiff ℝ ∞ q := hφ.sub (contDiff_const.mul hψ)
    have hqc : HasCompactSupport q := hφc.sub hψc.mul_left
    have hqs : tsupport q ⊆ Ioo l r :=
      (tsupport_sub _ _).trans (union_subset hφs (tsupport_mul_subset_right.trans hψs))
    have hφi := hφ.continuous.integrable_of_hasCompactSupport hφc (μ := volume)
    have hψint := hψ.continuous.integrable_of_hasCompactSupport hψc (μ := volume)
    have hqi : (∫ x, q x) = 0 := by
      rw [show q = fun x => φ x - (∫ t, φ t) * ψ x from rfl,
        integral_sub hφi (hψint.const_mul _), integral_const_mul, hψi, mul_one, sub_self]
    obtain ⟨η, hη, hηc, hηs, hdη⟩ := exists_compactSupport_primitive hq hqc hqs hqi hlr
    have hid := hweak η hη hηc hηs
    simp_rw [hdη, q, sub_mul, mul_assoc] at hid
    rw [integral_sub (integrable_mul_test hC hφ.continuous hφc hφs)
      ((integrable_mul_test hC hψ.continuous hψc hψs).const_mul _),
      integral_const_mul] at hid
    simp_rw [mul_sub]
    rw [integral_sub (integrable_mul_test hC hφ.continuous hφc hφs) (hφi.mul_const _),
      integral_mul_const]
    exact hid
  have hcont : ContinuousOn (fun x => C x - c) (Ioo l r) := hC.sub continuousOn_const
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) (hcont.locallyIntegrableOn measurableSet_Ioo)
    (fun φ hφ hφc hφs => by simpa only [smul_eq_mul] using htest φ hφ hφc hφs)
  have hzero : EqOn (fun x => C x - c) (fun _ => 0) (Ioo l r) :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' measurableSet_Ioo).mpr hae)
      isOpen_Ioo hcont continuousOn_const
  exact ⟨c, fun x hx => sub_eq_zero.mp (hzero hx)⟩

theorem intervalIntegral_eq_sub_of_weakDerivative {A B : ℝ → ℝ} {l r a b : ℝ}
    (hA : ContinuousOn A (Ioo l r)) (hB : ContinuousOn B (Ioo l r))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo l r →
      (∫ x, η x * A x) = -(∫ x, deriv η x * B x))
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) :
    (∫ x in a..b, A x) = B b - B a := by
  let F : ℝ → ℝ := fun x => ∫ t in a..x, A t
  have hFder (x : ℝ) (hx : x ∈ Ioo l r) : HasDerivAt F (A x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hA.mono (ordConnected_Ioo.uIcc_subset ha hx)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hA x hx)
      (hA.continuousAt (isOpen_Ioo.mem_nhds hx))
  have hF : ContinuousOn F (Ioo l r) :=
    fun x hx => (hFder x hx).continuousAt.continuousWithinAt
  have hFweak (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Ioo l r) :
      (∫ x, η x * A x) = -(∫ x, deriv η x * F x) := by
    apply integral_mul_deriv_eq_deriv_mul_of_integrable
    · intro x _
      exact (hη.differentiable (by simp) x).hasDerivAt
    · intro x hx
      exact hFder x (hηs hx)
    · exact integrable_mul_test hA hη.continuous hηc hηs
    · exact integrable_mul_test hF (hη.continuous_deriv (by simp)) hηc.deriv
        (tsupport_deriv_subset.trans hηs)
    · exact integrable_mul_test hF hη.continuous hηc hηs
  have hzero (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Ioo l r) :
      (∫ x, deriv η x * (B x - F x)) = 0 := by
    simp_rw [mul_sub]
    rw [integral_sub
      (integrable_mul_test hB (hη.continuous_deriv (by simp)) hηc.deriv
        (tsupport_deriv_subset.trans hηs))
      (integrable_mul_test hF (hη.continuous_deriv (by simp)) hηc.deriv
        (tsupport_deriv_subset.trans hηs))]
    linarith [hweak η hη hηc hηs, hFweak η hη hηc hηs]
  obtain ⟨c, hc⟩ := eqOn_const_of_integral_deriv_mul_eq_zero
    (ha.1.trans ha.2) (hB.sub hF) hzero
  have hca := hc ha
  have hcb := hc hb
  have hFa : F a = 0 := by simp [F]
  change B a - F a = c at hca
  change B b - (∫ x in a..b, A x) = c at hcb
  rw [hFa] at hca
  linarith

theorem intervalIntegral_eq_sub_of_weakDerivative_Icc {A B : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b →
      (∫ x, η x * A x) = -(∫ x, deriv η x * B x)) :
    (∫ x in a..b, A x) = B b - B a := by
  let F : ℝ → ℝ := fun x => ∫ t in a..x, A t
  have hA' : ContinuousOn A (Set.uIcc a b) := by simpa only [uIcc_of_le hab.le] using hA
  have hF : ContinuousOn F (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hA'.intervalIntegrable
        (left_mem_uIcc : a ∈ Set.uIcc a b)
  have hFder (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt F (A x) x := by
    apply intervalIntegral.integral_hasDerivAt_right
    · apply ContinuousOn.intervalIntegrable
      exact hA.mono (ordConnected_Icc.uIcc_subset (left_mem_Icc.2 hab.le)
        (Ioo_subset_Icc_self hx))
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hA.mono Ioo_subset_Icc_self) x hx
    · exact (hA.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hx)
  have hC : ContinuousOn (fun x => B x - F x) (Ioo a b) :=
    (hB.mono Ioo_subset_Icc_self).sub (hF.mono Ioo_subset_Icc_self)
  have hzero (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Ioo a b) :
      (∫ x, deriv η x * (B x - F x)) = 0 := by
    have hFweak : (∫ x, η x * A x) = -(∫ x, deriv η x * F x) := by
      apply integral_mul_deriv_eq_deriv_mul_of_integrable
      · intro x _
        exact (hη.differentiable (by simp) x).hasDerivAt
      · intro x hx
        exact hFder x (hηs hx)
      · exact integrable_mul_test (hA.mono Ioo_subset_Icc_self) hη.continuous hηc hηs
      · exact integrable_mul_test (hF.mono Ioo_subset_Icc_self)
          (hη.continuous_deriv (by simp)) hηc.deriv
          (tsupport_deriv_subset.trans hηs)
      · exact integrable_mul_test (hF.mono Ioo_subset_Icc_self) hη.continuous hηc hηs
    simp_rw [mul_sub]
    rw [integral_sub
      (integrable_mul_test (hB.mono Ioo_subset_Icc_self) (hη.continuous_deriv (by simp)) hηc.deriv
        (tsupport_deriv_subset.trans hηs))
      (integrable_mul_test (hF.mono Ioo_subset_Icc_self) (hη.continuous_deriv (by simp)) hηc.deriv
        (tsupport_deriv_subset.trans hηs))]
    linarith [hweak η hη hηc hηs, hFweak]
  obtain ⟨c, hc⟩ := eqOn_const_of_integral_deriv_mul_eq_zero hab hC hzero
  have hcc : EqOn (fun x => B x - F x) (fun _ => c) (Icc a b) :=
    hc.of_subset_closure (hB.sub hF) continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  have hca := hcc (left_mem_Icc.2 hab.le)
  have hcb := hcc (right_mem_Icc.2 hab.le)
  have hFa : F a = 0 := by simp [F]
  change B a - F a = c at hca
  change B b - (∫ x in a..b, A x) = c at hcb
  rw [hFa] at hca
  linarith

end Poincare.Analysis.WeakDerivative
