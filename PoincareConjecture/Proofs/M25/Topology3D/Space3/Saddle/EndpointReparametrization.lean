import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic










set_option autoImplicit false

open Set Function Filter MeasureTheory Metric
open scoped ContDiff Manifold Topology BigOperators

namespace PoincareConjecture.M25.Topology3D


set_option maxHeartbeats 1500000 in

set_option linter.unusedVariables false in



theorem exists_saddle_endpoint_reparametrizations
    (n : ℕ) (eta : ℝ) (heta : 0 < eta) (hetaSmall : eta < 1 / 8)
    (f0 f1 : Fin n → ℝ → ℝ)
    (hf0 : ∀ i, ContDiffOn ℝ ∞ (f0 i) (Ioo (-eta) eta))
    (hf1 : ∀ i, ContDiffOn ℝ ∞ (f1 i) (Ioo (1 - eta) (1 + eta)))
    (hzero : ∀ i, f0 i 0 = 0) (hone : ∀ i, f1 i 1 = 1)
    (hderiv0 : ∀ i, 0 < deriv (f0 i) 0)
    (hderiv1 : ∀ i, 0 < deriv (f1 i) 1) :
    ∃ (nu : ℝ)
      (Theta : Fin n → Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞),
      0 < nu ∧ nu < eta / 8 ∧
      ∀ i,
        StrictMono (Theta i) ∧ StrictMono (Theta i).symm ∧
        (∀ t : ℝ, 0 < deriv (Theta i) t) ∧
        Theta i 0 = 0 ∧ Theta i 1 = 1 ∧
        MapsTo (Theta i) (Icc (-nu) (1 + nu)) (Ioo (-eta) (1 + eta)) ∧
        MapsTo (Theta i) (Icc (-nu) nu) (Ioo (-eta) eta) ∧
        MapsTo (Theta i) (Icc (1 - nu) (1 + nu)) (Ioo (1 - eta) (1 + eta)) ∧
        EqOn (fun t => f0 i (Theta i t)) id (Icc (-nu) nu) ∧
        EqOn (fun t => f1 i (Theta i t)) id (Icc (1 - nu) (1 + nu)) ∧
        EqOn (Theta i).symm (f0 i) (Theta i '' Icc (-nu) nu) ∧
        EqOn (Theta i).symm (f1 i) (Theta i '' Icc (1 - nu) (1 + nu)) ∧
        Theta i '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 ∧
        Theta i '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 ∧
        (Theta i).symm '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 ∧
        (Theta i).symm '' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
  classical
  have hprimitive (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (m : ℝ)
      (hm : 0 < m) (hvm : ∀ t, m ≤ v t) :
      ∃ P : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
        (∀ t, P t = ∫ s in (0 : ℝ)..t, v s) ∧
        StrictMono P ∧ ∀ t, deriv P t = v t := by
    let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, v s
    have hvi (s t : ℝ) : IntervalIntegrable v volume s t :=
      hv.continuous.intervalIntegrable s t
    have hFd (t : ℝ) : HasDerivAt F (v t) t :=
      intervalIntegral.integral_hasDerivAt_right (hvi 0 t)
        hv.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hv.continuous.continuousAt
    have hF : ContDiff ℝ ∞ F := by
      apply contDiff_infty_iff_deriv.mpr
      refine ⟨fun t => (hFd t).differentiableAt, ?_⟩
      have heq : deriv F = v := funext fun t => (hFd t).deriv
      rw [heq]
      exact hv
    have hFp (t : ℝ) : 0 < deriv F t := by
      rw [(hFd t).deriv]
      exact hm.trans_le (hvm t)
    have hFm : StrictMono F := strictMono_of_deriv_pos hFp
    have hFs : Surjective F := by
      intro z
      let R : ℝ := (|z| + 1) / m
      have hR : 0 < R := div_pos (by positivity) hm
      have hRm : R * m = |z| + 1 := div_mul_cancel₀ _ hm.ne'
      have hplus : R * m ≤ F R := by
        have hi := intervalIntegral.integral_mono_on hR.le
          (continuous_const.intervalIntegrable 0 R) (hvi 0 R)
          (fun t _ => hvm t)
        simpa only [intervalIntegral.integral_const, smul_eq_mul,
          sub_zero] using hi
      have hminus : F (-R) ≤ -(R * m) := by
        have hi := intervalIntegral.integral_mono_on (by linarith : -R ≤ 0)
          (continuous_const.intervalIntegrable (-R) 0) (hvi (-R) 0)
          (fun t _ => hvm t)
        simp only [intervalIntegral.integral_const, smul_eq_mul,
          zero_sub, neg_neg] at hi
        dsimp [F]
        rw [intervalIntegral.integral_symm]
        linarith
      apply intermediate_value_univ (-R) R hF.continuous
      exact ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩
    have hfdiff : ∀ t ∈ (univ : Set ℝ), ∃ A : ℝ ≃L[ℝ] ℝ,
        HasFDerivAt F (A : ℝ →L[ℝ] ℝ) t := by
      intro t _
      exact ⟨ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 (v t) (hm.trans_le (hvm t)).ne'),
        (hFd t).hasFDerivAt_equiv (hm.trans_le (hvm t)).ne'⟩
    let chart := smoothOpenChart F isOpen_univ hF.contDiffOn
      hfdiff hFm.injective.injOn
    have htarget : chart.target = univ := by
      change F '' univ = univ
      exact image_univ_of_surjective hFs
    have hinverse : ContDiff ℝ ∞ chart.symm := by
      apply contDiffOn_univ.mp
      rw [← htarget]
      exact smoothOpenChart_symm_contDiffOn F isOpen_univ hF.contDiffOn
        hfdiff hFm.injective.injOn
    let P : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
      toEquiv := {
        toFun := chart
        invFun := chart.symm
        left_inv := fun t => chart.left_inv (mem_univ t)
        right_inv := fun t => chart.right_inv (by rw [htarget]; exact mem_univ t) }
      contMDiff_toFun := hF.contMDiff
      contMDiff_invFun := hinverse.contMDiff }
    exact ⟨P, fun _ => rfl, hFm, fun t => (hFd t).deriv⟩
  have hwindow (f : ℝ → ℝ) (a : ℝ)
      (hf : ContDiffOn ℝ ∞ f (Ioo (a - eta) (a + eta)))
      (hpos : 0 < deriv f a) :
      ∃ r : ℝ, 0 < r ∧ r < eta / 2 ∧
        ∀ t ∈ Icc (a - r) (a + r),
          t ∈ Ioo (a - eta) (a + eta) ∧
          deriv f a / 2 ≤ deriv f t ∧ deriv f t ≤ deriv f a + 1 := by
    have ha : a ∈ Ioo (a - eta) (a + eta) := ⟨by linarith, by linarith⟩
    have hc : ContinuousAt (deriv f) a :=
      (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt
        (isOpen_Ioo.mem_nhds ha)
    have heder : ∀ᶠ t in 𝓝 a,
        deriv f t ∈ Ioo (deriv f a / 2) (deriv f a + 1) :=
      hc.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have he : ∀ᶠ t in 𝓝 a,
        t ∈ Ioo (a - eta) (a + eta) ∧
          deriv f a / 2 < deriv f t ∧ deriv f t < deriv f a + 1 := by
      filter_upwards [isOpen_Ioo.mem_nhds ha, heder] with t ht hd
      exact ⟨ht, hd.1, hd.2⟩
    obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp he
    let r : ℝ := min eps eta / 4
    have hr : 0 < r := by dsimp [r]; positivity
    have hre : r < eps := by dsimp [r]; linarith [min_le_left eps eta]
    have hrη : r < eta / 2 := by dsimp [r]; linarith [min_le_right eps eta]
    refine ⟨r, hr, hrη, ?_⟩
    intro t ht
    have hd : dist t a < eps := by
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans_lt hre
    exact ⟨(hball hd).1, (hball hd).2.1.le, (hball hd).2.2.le⟩
  have hsingle (i : Fin n) :
      ∃ (d : ℝ) (T : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞),
        0 < d ∧ d < eta / 8 ∧ StrictMono T ∧ StrictMono T.symm ∧
        (∀ t : ℝ, 0 < deriv T t) ∧ T 0 = 0 ∧ T 1 = 1 ∧
        MapsTo T (Icc (-d) d) (Ioo (-eta) eta) ∧
        MapsTo T (Icc (1 - d) (1 + d)) (Ioo (1 - eta) (1 + eta)) ∧
        EqOn (fun t => f0 i (T t)) id (Icc (-d) d) ∧
        EqOn (fun t => f1 i (T t)) id (Icc (1 - d) (1 + d)) := by
    obtain ⟨r0, hr0, hr0η, hlocal0⟩ := hwindow (f0 i) 0
      (by simpa only [zero_sub, zero_add] using hf0 i) (hderiv0 i)
    obtain ⟨r1, hr1, hr1η, hlocal1⟩ := hwindow (f1 i) 1 (hf1 i) (hderiv1 i)
    simp only [zero_sub, zero_add] at hlocal0
    let m : ℝ := min (1 / 4) (min (deriv (f0 i) 0 / 2) (deriv (f1 i) 1 / 2))
    let M : ℝ := max 1 (max (deriv (f0 i) 0 + 1) (deriv (f1 i) 1 + 1))
    have hm : 0 < m := lt_min (by norm_num)
      (lt_min (half_pos (hderiv0 i)) (half_pos (hderiv1 i)))
    have hm4 : m ≤ 1 / 4 := min_le_left _ _
    have hm0 : m ≤ deriv (f0 i) 0 / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hm1 : m ≤ deriv (f1 i) 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hM0 : deriv (f0 i) 0 + 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hM2 : deriv (f1 i) 1 + 1 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    have hM : 0 < M := zero_lt_one.trans_le hM1
    have hchoice : 0 < min (min (r0 / 4) (r1 / 4))
        (min (1 / 64) (1 / (32 * (M + 1)))) := by positivity
    obtain ⟨b, hb, hbSmall⟩ := exists_between hchoice
    have hb0 : b < r0 / 4 := (lt_min_iff.mp (lt_min_iff.mp hbSmall).1).1
    have hb1 : b < r1 / 4 := (lt_min_iff.mp (lt_min_iff.mp hbSmall).1).2
    have hb64 : b < 1 / 64 := (lt_min_iff.mp (lt_min_iff.mp hbSmall).2).1
    have hbM : b < 1 / (32 * (M + 1)) :=
      (lt_min_iff.mp (lt_min_iff.mp hbSmall).2).2
    have hbη : b < eta := by linarith
    have hcut (a : ℝ) : ∃ chi : ℝ → ℝ,
        ContDiff ℝ ∞ chi ∧ tsupport chi ⊆ Ioo (a - 2 * b) (a + 2 * b) ∧
        (∀ t, chi t ∈ Icc (0 : ℝ) 1) ∧
        EqOn chi (fun _ => 1) (Icc (a - b) (a + b)) := by
      obtain ⟨chi, hc, _, hs, ho, hbounds⟩ := exists_compact_smooth_cutoff
        (K := Icc (a - b) (a + b)) (U := Ioo (a - 2 * b) (a + 2 * b))
        isCompact_Icc isOpen_Ioo (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      exact ⟨chi, hc, hs, hbounds, fun t ht => subset_of_mem_nhdsSet ho ht⟩
    obtain ⟨chi0, hc0, hs0, hbd0, hone0⟩ := hcut 0
    obtain ⟨chi1, hc1, hs1, hbd1, hone1⟩ := hcut 1
    simp only [zero_sub, zero_add] at hs0 hone0
    have hz0 (t : ℝ) (ht : t ≤ -2 * b ∨ 2 * b ≤ t) : chi0 t = 0 := by
      by_contra hn
      have hs := hs0 (subset_tsupport chi0 hn)
      rcases ht with ht | ht <;> linarith [hs.1, hs.2]
    have hz1 (t : ℝ) (ht : t ≤ 1 - 2 * b ∨ 1 + 2 * b ≤ t) : chi1 t = 0 := by
      by_contra hn
      have hs := hs1 (subset_tsupport chi1 hn)
      rcases ht with ht | ht <;> linarith [hs.1, hs.2]
    have hd0 (t : ℝ) (ht : chi0 t ≠ 0) :
        t ∈ Ioo (-eta) eta ∧ m ≤ deriv (f0 i) t ∧ deriv (f0 i) t ≤ M := by
      have hs := hs0 (subset_tsupport chi0 ht)
      have hl := hlocal0 t ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact ⟨hl.1, hm0.trans hl.2.1, hl.2.2.trans hM0⟩
    have hd1 (t : ℝ) (ht : chi1 t ≠ 0) :
        t ∈ Ioo (1 - eta) (1 + eta) ∧
          m ≤ deriv (f1 i) t ∧ deriv (f1 i) t ≤ M := by
      have hs := hs1 (subset_tsupport chi1 ht)
      have hl := hlocal1 t ⟨by linarith [hs.1], by linarith [hs.2]⟩
      exact ⟨hl.1, hm1.trans hl.2.1, hl.2.2.trans hM2⟩
    have hsupport0 : tsupport chi0 ⊆ Ioo (-eta) eta := by
      intro t ht
      have hs := hs0 ht
      exact (hlocal0 t ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
    have hsupport1 : tsupport chi1 ⊆ Ioo (1 - eta) (1 + eta) := by
      intro t ht
      have hs := hs1 ht
      exact (hlocal1 t ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
    let v0 : ℝ → ℝ := fun t => (1 / 4 : ℝ) +
      chi0 t * (deriv (f0 i) t - 1 / 4) + chi1 t * (deriv (f1 i) t - 1 / 4)
    have hv0 : ContDiff ℝ ∞ v0 := by
      have h0 := contDiff_cutoff_smul isOpen_Ioo chi0 hc0 hsupport0
        (fun t => deriv (f0 i) t - 1 / 4)
        (((hf0 i).deriv_of_isOpen isOpen_Ioo (by simp)).sub contDiffOn_const)
      have h1 := contDiff_cutoff_smul isOpen_Ioo chi1 hc1 hsupport1
        (fun t => deriv (f1 i) t - 1 / 4)
        (((hf1 i).deriv_of_isOpen isOpen_Ioo (by simp)).sub contDiffOn_const)
      simpa only [v0, smul_eq_mul] using (contDiff_const.add h0).add h1
    have hvrange (t : ℝ) : m ≤ v0 t ∧ v0 t ≤ M := by
      by_cases h0 : chi0 t = 0
      · by_cases h1 : chi1 t = 0
        · simp only [v0, h0, h1, zero_mul, add_zero]
          exact ⟨hm4, by linarith⟩
        · have h1b := hd1 t h1
          have hc := hbd1 t
          have hlow := add_nonneg (mul_nonneg hc.1 (sub_nonneg.mpr h1b.2.1))
            (mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hm4))
          have hhigh := add_nonneg (mul_nonneg hc.1 (sub_nonneg.mpr h1b.2.2))
            (mul_nonneg (sub_nonneg.mpr hc.2) (by linarith : 0 ≤ M - 1 / 4))
          simp only [v0, h0, zero_mul, add_zero]
          constructor <;> nlinarith
      · have h1 : chi1 t = 0 := by
          apply hz1 t
          left
          have hs := hs0 (subset_tsupport chi0 h0)
          linarith [hs.2]
        have h0b := hd0 t h0
        have hc := hbd0 t
        have hlow := add_nonneg (mul_nonneg hc.1 (sub_nonneg.mpr h0b.2.1))
          (mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hm4))
        have hhigh := add_nonneg (mul_nonneg hc.1 (sub_nonneg.mpr h0b.2.2))
          (mul_nonneg (sub_nonneg.mpr hc.2) (by linarith : 0 ≤ M - 1 / 4))
        simp only [v0, h1, zero_mul, add_zero]
        constructor <;> nlinarith
    have hmid (t : ℝ) (ht : t ∈ Icc (2 * b) (1 - 2 * b)) : v0 t = 1 / 4 := by
      simp only [v0, hz0 t (Or.inr ht.1), hz1 t (Or.inl ht.2), zero_mul, add_zero]
    have hvi0 (a z : ℝ) : IntervalIntegrable v0 volume a z :=
      hv0.continuous.intervalIntegrable a z
    let I : ℝ := ∫ t in (0 : ℝ)..1, v0 t
    have hIupper : I ≤ 1 / 4 + 4 * b * M := by
      have hl := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * b)
        (hvi0 0 (2 * b)) (continuous_const.intervalIntegrable 0 (2 * b))
        (fun t _ => (hvrange t).2)
      have hr := intervalIntegral.integral_mono_on (by linarith : 1 - 2 * b ≤ 1)
        (hvi0 (1 - 2 * b) 1) (continuous_const.intervalIntegrable (1 - 2 * b) 1)
        (fun t _ => (hvrange t).2)
      have hmiddle : (∫ t in (2 * b)..(1 - 2 * b), v0 t) = (1 - 4 * b) / 4 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1 / 4 : ℝ)) (by
          intro t ht
          rw [uIcc_of_le (by linarith : 2 * b ≤ 1 - 2 * b)] at ht
          exact hmid t ht), intervalIntegral.integral_const, smul_eq_mul]
        ring
      have hs := intervalIntegral.integral_add_adjacent_intervals
        (hvi0 0 (2 * b)) (hvi0 (2 * b) (1 - 2 * b))
      have ht := intervalIntegral.integral_add_adjacent_intervals
        (hvi0 0 (1 - 2 * b)) (hvi0 (1 - 2 * b) 1)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hl hr
      dsimp [I]
      linarith
    have hIlt : I < 1 := by
      have hbmul := (lt_div_iff₀ (by positivity : 0 < 32 * (M + 1))).mp hbM
      have hbpos : 0 < b * M := mul_pos hb hM
      nlinarith
    obtain ⟨p, hp, _, hps, hpnear, hpbd⟩ := exists_compact_smooth_cutoff
      (K := ({(1 / 2 : ℝ)} : Set ℝ)) (U := Ioo (1 / 3 : ℝ) (2 / 3))
      isCompact_singleton isOpen_Ioo (by intro t ht; rcases ht with rfl; norm_num)
    have hpHalf : p (1 / 2) = 1 := subset_of_mem_nhdsSet hpnear (mem_singleton _)
    let B : ℝ := ∫ t in (0 : ℝ)..1, p t
    have hB : 0 < B := intervalIntegral.integral_pos (by norm_num)
      hp.continuous.continuousOn (fun t _ => (hpbd t).1)
      ⟨1 / 2, by norm_num, by rw [hpHalf]; norm_num⟩
    let lam : ℝ := (1 - I) / B
    have hlam : 0 < lam := div_pos (sub_pos.mpr hIlt) hB
    let v : ℝ → ℝ := fun t => v0 t + lam * p t
    have hv : ContDiff ℝ ∞ v := hv0.add (contDiff_const.mul hp)
    have hvm (t : ℝ) : m ≤ v t :=
      (hvrange t).1.trans (le_add_of_nonneg_right (mul_nonneg hlam.le (hpbd t).1))
    have hint : (∫ t in (0 : ℝ)..1, v t) = 1 := by
      change (∫ t in (0 : ℝ)..1, v0 t + lam * p t) = 1
      have hip : IntervalIntegrable (fun t => lam * p t) volume 0 1 :=
        ((continuous_const (y := lam)).mul hp.continuous).intervalIntegrable 0 1
      rw [intervalIntegral.integral_add (hvi0 0 1) hip, intervalIntegral.integral_const_mul]
      change I + lam * B = 1
      dsimp [lam]
      rw [div_mul_cancel₀ _ hB.ne']
      ring
    have hpzero (t : ℝ) (ht : t ≤ 1 / 3 ∨ 2 / 3 ≤ t) : p t = 0 := by
      by_contra hn
      have hs := hps (subset_tsupport p hn)
      rcases ht with ht | ht <;> linarith [hs.1, hs.2]
    have hvInitial (t : ℝ) (ht : t ∈ Icc (-b) b) : v t = deriv (f0 i) t := by
      simp only [v, v0, hone0 ht,
        hz1 t (Or.inl (by linarith [ht.2])),
        hpzero t (Or.inl (by linarith [ht.2])), one_mul, zero_mul, mul_zero, add_zero]
      ring
    have hvTerminal (t : ℝ) (ht : t ∈ Icc (1 - b) (1 + b)) : v t = deriv (f1 i) t := by
      simp only [v, v0, hone1 ht,
        hz0 t (Or.inr (by linarith [ht.1])),
        hpzero t (Or.inr (by linarith [ht.1])), one_mul, zero_mul, mul_zero, add_zero]
      ring
    obtain ⟨P, hPint, hPmono, hPd⟩ := hprimitive v hv m hm hvm
    have hP0 : P 0 = 0 := by rw [hPint]; simp
    have hP1 : P 1 = 1 := (hPint 1).trans hint
    have hu0 : Ioo (-b) b ⊆ Ioo (-eta) eta := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hu1 : Ioo (1 - b) (1 + b) ⊆ Ioo (1 - eta) (1 + eta) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hPInitial : EqOn P (f0 i) (Ioo (-b) b) := by
      apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-b) b).isPreconnected
        (P.contDiff.differentiable (by simp)).differentiableOn
        (((hf0 i).mono hu0).differentiableOn (by simp))
        (fun t ht => (hPd t).trans (hvInitial t ⟨ht.1.le, ht.2.le⟩))
        (show (0 : ℝ) ∈ Ioo (-b) b from ⟨by linarith, hb⟩)
      exact hP0.trans (hzero i).symm
    have hPTerminal : EqOn P (f1 i) (Ioo (1 - b) (1 + b)) := by
      apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (1 - b) (1 + b)).isPreconnected
        (P.contDiff.differentiable (by simp)).differentiableOn
        (((hf1 i).mono hu1).differentiableOn (by simp))
        (fun t ht => (hPd t).trans (hvTerminal t ⟨ht.1.le, ht.2.le⟩))
        (show (1 : ℝ) ∈ Ioo (1 - b) (1 + b) from ⟨by linarith, by linarith⟩)
      exact hP1.trans (hone i).symm
    let T := P.symm
    have hT0 : T 0 = 0 := by
      apply P.toEquiv.injective
      change P (P.symm 0) = P 0
      rw [P.apply_symm_apply, hP0]
    have hT1 : T 1 = 1 := by
      apply P.toEquiv.injective
      change P (P.symm 1) = P 1
      rw [P.apply_symm_apply, hP1]
    have hTderiv (t : ℝ) : 0 < deriv T t := by
      have hpos : 0 < deriv P (T t) := by rw [hPd]; exact hm.trans_le (hvm _)
      have hdt : HasDerivAt T (deriv P (T t))⁻¹ t :=
        (P.contDiff.differentiable (by simp) (T t)).hasDerivAt.of_local_left_inverse
          T.continuous.continuousAt hpos.ne'
          (Eventually.of_forall fun s => P.apply_symm_apply s)
      rw [hdt.deriv]
      exact inv_pos.mpr hpos
    have hTmono : StrictMono T := strictMono_of_deriv_pos hTderiv
    have hinvMono : StrictMono T.symm := hPmono
    have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), T t ∈ Ioo (-b) b :=
      T.continuous.continuousAt.eventually
        (by rw [hT0]; exact Ioo_mem_nhds (by linarith) hb)
    have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), T t ∈ Ioo (1 - b) (1 + b) :=
      T.continuous.continuousAt.eventually
        (by rw [hT1]; exact Ioo_mem_nhds (by linarith) (by linarith))
    obtain ⟨eps0, heps0, hball0⟩ := Metric.eventually_nhds_iff.mp hnear0
    obtain ⟨eps1, heps1, hball1⟩ := Metric.eventually_nhds_iff.mp hnear1
    let d : ℝ := min (eta / 8) (min eps0 eps1) / 2
    have hd : 0 < d := by dsimp [d]; positivity
    have hdη : d < eta / 8 := by dsimp [d]; linarith [min_le_left (eta / 8) (min eps0 eps1)]
    have hd0 : d < eps0 := by
      have hh := (min_le_right (eta / 8) (min eps0 eps1)).trans (min_le_left eps0 eps1)
      dsimp [d]
      linarith
    have hd1 : d < eps1 := by
      have hh := (min_le_right (eta / 8) (min eps0 eps1)).trans (min_le_right eps0 eps1)
      dsimp [d]
      linarith
    have himage0 (t : ℝ) (ht : t ∈ Icc (-d) d) : T t ∈ Ioo (-b) b := by
      apply hball0
      rw [Real.dist_eq, sub_zero]
      exact (abs_le.mpr ht).trans_lt hd0
    have himage1 (t : ℝ) (ht : t ∈ Icc (1 - d) (1 + d)) :
        T t ∈ Ioo (1 - b) (1 + b) := by
      apply hball1
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans_lt hd1
    refine ⟨d, T, hd, hdη, hTmono, hinvMono, hTderiv, hT0, hT1,
      (fun t ht => hu0 (himage0 t ht)), (fun t ht => hu1 (himage1 t ht)), ?_, ?_⟩
    · intro t ht
      calc
        f0 i (T t) = P (T t) := (hPInitial (himage0 t ht)).symm
        _ = t := P.apply_symm_apply t
    · intro t ht
      calc
        f1 i (T t) = P (T t) := (hPTerminal (himage1 t ht)).symm
        _ = t := P.apply_symm_apply t
  choose d T hd hdη hmono hinvMono hderiv hT0 hT1 hmap0 hmap1 heq0 heq1 using hsingle
  let A : ℝ := 1 + ∑ i : Fin n, 1 / d i
  have hA : 0 < A := by
    have hs : 0 ≤ ∑ i : Fin n, 1 / d i :=
      Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hd i)).le
    dsimp [A]
    linarith
  let nu : ℝ := min (eta / 8) (1 / A) / 2
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hnuη : nu < eta / 8 := by
    dsimp [nu]
    linarith [min_le_left (eta / 8) (1 / A)]
  have hnui (i : Fin n) : nu < d i := by
    have hs : 1 / d i ≤ ∑ j : Fin n, 1 / d j :=
      Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hd j)).le) (Finset.mem_univ i)
    have hAi : 1 / d i < A := by dsimp [A]; linarith
    have hinv : 1 / A < d i := by
      simpa only [one_div_one_div] using
        one_div_lt_one_div_of_lt (one_div_pos.mpr (hd i)) hAi
    have hnule : nu ≤ 1 / A := by
      dsimp [nu]
      linarith [min_le_right (eta / 8) (1 / A), one_div_pos.mpr hA]
    exact hnule.trans_lt hinv
  refine ⟨nu, T, hnu, hnuη, ?_⟩
  intro i
  have hsub0 : Icc (-nu) nu ⊆ Icc (-(d i)) (d i) := by
    intro t ht
    exact ⟨by linarith [ht.1, hnui i], by linarith [ht.2, hnui i]⟩
  have hsub1 : Icc (1 - nu) (1 + nu) ⊆ Icc (1 - d i) (1 + d i) := by
    intro t ht
    exact ⟨by linarith [ht.1, hnui i], by linarith [ht.2, hnui i]⟩
  have hm0 : MapsTo (T i) (Icc (-nu) nu) (Ioo (-eta) eta) :=
    fun t ht => hmap0 i (hsub0 ht)
  have hm1 : MapsTo (T i) (Icc (1 - nu) (1 + nu)) (Ioo (1 - eta) (1 + eta)) :=
    fun t ht => hmap1 i (hsub1 ht)
  have he0 : EqOn (fun t => f0 i (T i t)) id (Icc (-nu) nu) :=
    fun t ht => heq0 i (hsub0 ht)
  have he1 : EqOn (fun t => f1 i (T i t)) id (Icc (1 - nu) (1 + nu)) :=
    fun t ht => heq1 i (hsub1 ht)
  have hmwhole : MapsTo (T i) (Icc (-nu) (1 + nu)) (Ioo (-eta) (1 + eta)) := by
    intro t ht
    have hleft := hm0 (show -nu ∈ Icc (-nu) nu from ⟨le_rfl, by linarith⟩)
    have hright := hm1 (show 1 + nu ∈ Icc (1 - nu) (1 + nu) from ⟨by linarith, le_rfl⟩)
    exact ⟨hleft.1.trans_le ((hmono i).monotone ht.1),
      ((hmono i).monotone ht.2).trans_lt hright.2⟩
  have hI0 : (T i).symm 0 = 0 := by
    apply (T i).toEquiv.injective
    change (T i) ((T i).symm 0) = (T i) 0
    rw [(T i).apply_symm_apply, hT0 i]
  have hI1 : (T i).symm 1 = 1 := by
    apply (T i).toEquiv.injective
    change (T i) ((T i).symm 1) = (T i) 1
    rw [(T i).apply_symm_apply, hT1 i]
  refine ⟨hmono i, hinvMono i, hderiv i, hT0 i, hT1 i, hmwhole, hm0, hm1,
    he0, he1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨t, ht, rfl⟩
    rw [(T i).symm_apply_apply]
    exact (he0 ht).symm
  · rintro x ⟨t, ht, rfl⟩
    rw [(T i).symm_apply_apply]
    exact (he1 ht).symm
  · simpa only [hT0 i, hT1 i] using
      (T i).continuous.image_Icc_of_strictMono (a := 0) (b := 1) (hmono i)
  · simpa only [hT0 i, hT1 i] using
      (T i).continuous.image_Ioo_of_strictMono (a := 0) (b := 1) (hmono i)
  · simpa only [hI0, hI1] using
      (T i).symm.continuous.image_Icc_of_strictMono (a := 0) (b := 1) (hinvMono i)
  · simpa only [hI0, hI1] using
      (T i).symm.continuous.image_Ioo_of_strictMono (a := 0) (b := 1) (hinvMono i)

end PoincareConjecture.M25.Topology3D
