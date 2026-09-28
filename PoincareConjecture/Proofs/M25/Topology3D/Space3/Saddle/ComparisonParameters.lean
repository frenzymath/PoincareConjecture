import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

set_option autoImplicit false

open Set Function MeasureTheory
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

theorem exists_saddle_comparison_parameters
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) :
    let l : ℝ := 3 * h
    let r : ℝ := 1 - 3 * h
    let eta : ℝ := h / 256
    let theta0 : ℝ := Real.arccos (3 / 4)
    let theta1 : ℝ := Real.arccos (1 / 2)
    let d : ℝ := theta1 / 2
    let speed : ℝ := d / eta
    let e : ℝ := theta0 - d
    let f : ℝ := theta0 + d
    ∃ (a b : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞),
      0 < eta ∧ eta < h / 128 ∧
      0 < e ∧ e < theta0 ∧ theta0 < theta1 ∧ theta1 < f ∧ f < Real.pi / 2 ∧
      StrictMono a ∧ StrictMono b ∧
      (∀ t : ℝ, 0 < deriv a t ∧ 0 < deriv b t) ∧
      a l = theta0 ∧ a r = 2 * Real.pi - theta0 ∧
      b (-theta0) = 0 ∧ b theta0 = 1 ∧
      (∀ t ∈ Icc (l - eta) (l + eta), a t = theta0 + speed * (t - l)) ∧
      (∀ t ∈ Icc (r - eta) (r + eta),
        a t = 2 * Real.pi - theta0 + speed * (t - r)) ∧
      (∀ theta : ℝ, theta ≤ -e → b theta = (theta + theta0) / speed) ∧
      (∀ theta : ℝ, e ≤ theta → b theta = 1 + (theta - theta0) / speed) ∧
      a '' Ioo (l - eta) (r + eta) = Ioo e (2 * Real.pi - e) ∧
      a '' Icc l r = Icc theta0 (2 * Real.pi - theta0) ∧
      a.symm '' Ioo e (2 * Real.pi - e) = Ioo (l - eta) (r + eta) ∧
      b '' Icc (-theta0) theta0 = Icc (0 : ℝ) 1 ∧
      b '' Ioo (-f) f = Ioo (-eta) (1 + eta) ∧
      b.symm '' Ioo (-eta) (1 + eta) = Ioo (-f) f := by
  let l : ℝ := 3 * h
  let r : ℝ := 1 - 3 * h
  let eta : ℝ := h / 256
  let theta0 : ℝ := Real.arccos (3 / 4)
  let theta1 : ℝ := Real.arccos (1 / 2)
  let d : ℝ := theta1 / 2
  let speed : ℝ := d / eta
  let e : ℝ := theta0 - d
  let f : ℝ := theta0 + d
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hgap : 4 * eta < r - l := by dsimp [eta, l, r]; linarith
  have hlr : l < r := by linarith
  have hetaSmall : eta < 1 / 4 := by dsimp [eta]; linarith
  have ht1 : theta1 = Real.pi / 3 := by
    dsimp [theta1]
    rw [← Real.cos_pi_div_three, Real.arccos_cos]
    · positivity
    · linarith [Real.pi_pos]
  have ht0low : Real.pi / 6 < theta0 := by
    have hc : (3 / 4 : ℝ) < Real.cos (Real.pi / 6) := by
      rw [Real.cos_pi_div_six]
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      have hn := Real.sqrt_nonneg (3 : ℝ)
      nlinarith
    have ha := Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 3 / 4)
      hc (Real.cos_le_one (Real.pi / 6))
    rw [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at ha
    exact ha
  have ht0hi : theta0 < theta1 :=
    Real.arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)
  have hd : d = Real.pi / 6 := by dsimp [d]; rw [ht1]; ring
  have hdpos : 0 < d := by rw [hd]; positivity
  have ht0pos : 0 < theta0 := by linarith [Real.pi_pos]
  have he : 0 < e := by dsimp [e]; rw [hd]; linarith
  have he0 : e < theta0 := by dsimp [e]; linarith
  have ht1f : theta1 < f := by dsimp [f]; rw [ht1, hd]; linarith
  have hfpi : f < Real.pi / 2 := by dsimp [f]; rw [hd]; rw [ht1] at ht0hi; linarith
  have hspos : 0 < speed := div_pos hdpos heta
  have hseta : speed * eta = d := div_mul_cancel₀ _ heta.ne'
  have hslarge : 2 * theta0 < speed := by
    apply (lt_div_iff₀ heta).mpr
    have hm := mul_lt_mul_of_pos_left hetaSmall (by linarith : 0 < 2 * theta0)
    rw [ht1] at ht0hi
    rw [hd]
    nlinarith
  let cut : ℝ → ℝ → ℝ → ℝ := fun x w t =>
    Real.smoothTransition ((t - (x - 2 * w)) / w) *
      Real.smoothTransition (((x + 2 * w) - t) / w)
  have hcutSmooth (x w : ℝ) : ContDiff ℝ ∞ (cut x w) :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const w)).mul
        (Real.smoothTransition.contDiff.comp
          ((contDiff_const.sub contDiff_id).div_const w))
  have hcutBounds (x w t : ℝ) : 0 ≤ cut x w t ∧ cut x w t ≤ 1 := by
    constructor
    · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    · simpa using mul_le_mul (Real.smoothTransition.le_one ((t - (x - 2 * w)) / w))
        (Real.smoothTransition.le_one (((x + 2 * w) - t) / w))
        (Real.smoothTransition.nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hcutZero (x w t : ℝ) (hw : 0 < w)
      (ht : t ≤ x - 2 * w ∨ x + 2 * w ≤ t) : cut x w t = 0 := by
    rcases ht with ht | ht
    · have hz : Real.smoothTransition ((t - (x - 2 * w)) / w) = 0 :=
        Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)
      simp only [cut, hz, zero_mul]
    · have hz : Real.smoothTransition (((x + 2 * w) - t) / w) = 0 :=
        Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le)
      simp only [cut, hz, mul_zero]
  have hcutOne (x w t : ℝ) (hw : 0 < w) (ht : t ∈ Icc (x - w) (x + w)) :
      cut x w t = 1 := by
    have h1 : Real.smoothTransition ((t - (x - 2 * w)) / w) = 1 :=
      Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw).mpr (by linarith [ht.1]))
    have h2 : Real.smoothTransition (((x + 2 * w) - t) / w) = 1 :=
      Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw).mpr (by linarith [ht.2]))
    simp only [cut, h1, h2, mul_one]
  have hci (x w s t : ℝ) : IntervalIntegrable (cut x w) volume s t :=
    (hcutSmooth x w).continuous.intervalIntegrable s t
  have hconstIntegral (v : ℝ → ℝ) (x y k : ℝ)
      (hv : ∀ t ∈ uIcc x y, v t = k) : (∫ t in x..y, v t) = (y - x) * k := by
    rw [intervalIntegral.integral_congr hv, intervalIntegral.integral_const, smul_eq_mul]

  have hprimitive (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (m : ℝ) (hm : 0 < m)
      (hvm : ∀ t, m ≤ v t) (x y : ℝ) :
      ∃ g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
        (∀ t, g t = y + ∫ s in x..t, v s) ∧ StrictMono g ∧ ∀ t, deriv g t = v t := by
    let F : ℝ → ℝ := fun t => y + ∫ s in x..t, v s
    have hvi (s t : ℝ) : IntervalIntegrable v volume s t :=
      hv.continuous.intervalIntegrable s t
    have hFd (t : ℝ) : HasDerivAt F (v t) t := by
      convert (intervalIntegral.integral_hasDerivAt_right (hvi x t)
        hv.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hv.continuous.continuousAt).const_add y using 1
    have hF : ContDiff ℝ ∞ F := by
      apply contDiff_infty_iff_deriv.mpr
      refine ⟨fun t => (hFd t).differentiableAt, ?_⟩
      have heq : deriv F = v := funext fun t => (hFd t).deriv
      rw [heq]
      exact hv
    have hFp (t : ℝ) : 0 < deriv F t := by rw [(hFd t).deriv]; exact hm.trans_le (hvm t)
    have hFm : StrictMono F := strictMono_of_deriv_pos hFp
    have hFs : Surjective F := by
      intro z
      let R : ℝ := (|z - y| + 1) / m
      have hR : 0 < R := div_pos (by positivity) hm
      have hRm : R * m = |z - y| + 1 := div_mul_cancel₀ _ hm.ne'
      have hplus : y + R * m ≤ F (x + R) := by
        have hi := intervalIntegral.integral_mono_on (by linarith : x ≤ x + R)
          (continuous_const.intervalIntegrable x (x + R)) (hvi x (x + R))
          (fun t _ => hvm t)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
        dsimp [F]
        linarith
      have hminus : F (x - R) ≤ y - R * m := by
        have hi := intervalIntegral.integral_mono_on (by linarith : x - R ≤ x)
          (continuous_const.intervalIntegrable (x - R) x) (hvi (x - R) x)
          (fun t _ => hvm t)
        simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
        dsimp [F]
        rw [intervalIntegral.integral_symm]
        linarith
      apply intermediate_value_univ (x - R) (x + R) hF.continuous
      exact ⟨by linarith [neg_abs_le (z - y)], by linarith [le_abs_self (z - y)]⟩
    have hfdiff : ∀ t ∈ (univ : Set ℝ), ∃ A : ℝ ≃L[ℝ] ℝ,
        HasFDerivAt F (A : ℝ →L[ℝ] ℝ) t := by
      intro t _
      let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (v t)
      have hp : 0 < v t := hm.trans_le (hvm t)
      have hLi : Injective L := by
        apply (injective_iff_map_eq_zero L).mpr
        intro s hs
        change s * v t = 0 at hs
        exact (mul_eq_zero.mp hs).resolve_right hp.ne'
      have hLs : Surjective L := by
        intro s
        refine ⟨s / v t, ?_⟩
        change s / v t * v t = s
        exact div_mul_cancel₀ _ hp.ne'
      obtain ⟨A, hA⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hLi, hLs⟩
      refine ⟨ContinuousLinearEquiv.ofUnit A, ?_⟩
      change HasFDerivAt F (A : ℝ →L[ℝ] ℝ) t
      rw [hA]
      exact (hFd t).hasFDerivAt
    let chart := smoothOpenChart F isOpen_univ hF.contDiffOn hfdiff hFm.injective.injOn
    have htarget : chart.target = univ := by
      change F '' univ = univ
      exact image_univ_of_surjective hFs
    have hinverse : ContDiff ℝ ∞ chart.symm := by
      apply contDiffOn_univ.mp
      rw [← htarget]
      exact smoothOpenChart_symm_contDiffOn F isOpen_univ hF.contDiffOn
        hfdiff hFm.injective.injOn
    let g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
      toEquiv := {
        toFun := chart
        invFun := chart.symm
        left_inv := fun t => chart.left_inv (mem_univ t)
        right_inv := fun t => chart.right_inv (by rw [htarget]; exact mem_univ t) }
      contMDiff_toFun := hF.contMDiff
      contMDiff_invFun := hinverse.contMDiff }
    exact ⟨g, fun _ => rfl, hFm, fun t => (hFd t).deriv⟩
  let E : ℝ → ℝ := fun t => cut l eta t + cut r eta t
  have hE : ContDiff ℝ ∞ E := (hcutSmooth l eta).add (hcutSmooth r eta)
  have hEi (s t : ℝ) : IntervalIntegrable E volume s t := hE.continuous.intervalIntegrable s t
  have hEb (t : ℝ) : 0 ≤ E t ∧ E t ≤ 1 := by
    refine ⟨add_nonneg (hcutBounds l eta t).1 (hcutBounds r eta t).1, ?_⟩
    by_cases ht : t ≤ l + 2 * eta
    · have hz := hcutZero r eta t heta (Or.inl (by linarith))
      simpa only [E, hz, add_zero] using (hcutBounds l eta t).2
    · have hz := hcutZero l eta t heta (Or.inr (by linarith))
      simpa only [E, hz, zero_add] using (hcutBounds r eta t).2
  have hEl (t : ℝ) (ht : t ∈ Icc (l - eta) (l + eta)) : E t = 1 := by
    dsimp only [E]
    rw [hcutOne l eta t heta ht, hcutZero r eta t heta (Or.inl (by linarith [ht.2]))]
    ring
  have hEr (t : ℝ) (ht : t ∈ Icc (r - eta) (r + eta)) : E t = 1 := by
    dsimp only [E]
    rw [hcutOne r eta t heta ht, hcutZero l eta t heta (Or.inr (by linarith [ht.1]))]
    ring
  let I : ℝ := ∫ t in l..r, E t
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => (hEb t).1)
  have hIbound : I ≤ 4 * eta := by
    have hleft : (∫ t in l..r, cut l eta t) ≤ 2 * eta := by
      have hz : (∫ t in (l + 2 * eta)..r, cut l eta t) = 0 := by
        rw [hconstIntegral _ _ _ 0]
        · ring
        · intro t ht
          rw [uIcc_of_le (by linarith : l + 2 * eta ≤ r)] at ht
          exact hcutZero l eta t heta (Or.inr ht.1)
      have ha := intervalIntegral.integral_add_adjacent_intervals
        (hci l eta l (l + 2 * eta)) (hci l eta (l + 2 * eta) r)
      rw [hz, add_zero] at ha
      rw [← ha]
      calc
        (∫ t in l..(l + 2 * eta), cut l eta t) ≤ ∫ _ in l..(l + 2 * eta), (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by linarith) (hci l eta l (l + 2 * eta))
            (continuous_const.intervalIntegrable _ _) (fun t _ => (hcutBounds l eta t).2)
        _ = 2 * eta := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hright : (∫ t in l..r, cut r eta t) ≤ 2 * eta := by
      have hz : (∫ t in l..(r - 2 * eta), cut r eta t) = 0 := by
        rw [hconstIntegral _ _ _ 0]
        · ring
        · intro t ht
          rw [uIcc_of_le (by linarith : l ≤ r - 2 * eta)] at ht
          exact hcutZero r eta t heta (Or.inl ht.2)
      have ha := intervalIntegral.integral_add_adjacent_intervals
        (hci r eta l (r - 2 * eta)) (hci r eta (r - 2 * eta) r)
      rw [hz, zero_add] at ha
      rw [← ha]
      calc
        (∫ t in (r - 2 * eta)..r, cut r eta t) ≤ ∫ _ in (r - 2 * eta)..r, (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by linarith) (hci r eta (r - 2 * eta) r)
            (continuous_const.intervalIntegrable _ _) (fun t _ => (hcutBounds r eta t).2)
        _ = 2 * eta := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hi : I = (∫ t in l..r, cut l eta t) + ∫ t in l..r, cut r eta t :=
      intervalIntegral.integral_add (hci l eta l r) (hci r eta l r)
    linarith
  let L : ℝ := 2 * Real.pi - 2 * theta0
  let B : ℝ := (L - speed * I) / (r - l - I)
  have hden : 0 < r - l - I := by linarith
  have hnum : 0 < L - speed * I := by
    have hi := mul_le_mul_of_nonneg_left hIbound hspos.le
    have hs4 : speed * (4 * eta) = 4 * d := by nlinarith [hseta]
    rw [hs4] at hi
    dsimp [L]
    rw [ht1] at ht0hi
    rw [hd] at hi
    linarith [Real.pi_pos]
  have hB : 0 < B := div_pos hnum hden
  have hBden : B * (r - l - I) = L - speed * I := div_mul_cancel₀ _ hden.ne'
  let v : ℝ → ℝ := fun t => speed * E t + B * (1 - E t)
  have hv : ContDiff ℝ ∞ v :=
    (contDiff_const.mul hE).add (contDiff_const.mul (contDiff_const.sub hE))
  have hvi (x y : ℝ) : IntervalIntegrable v volume x y := hv.continuous.intervalIntegrable x y
  have hvm (t : ℝ) : min speed B ≤ v t := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_left speed B) (hEb t).1
    have h2 := mul_le_mul_of_nonneg_right (min_le_right speed B) (sub_nonneg.mpr (hEb t).2)
    dsimp [v]
    nlinarith
  obtain ⟨a, ha, ham, had⟩ := hprimitive v hv (min speed B) (lt_min hspos hB) hvm l theta0
  have ha0 : a l = theta0 := by rw [ha]; simp
  have hval : (∫ t in l..r, v t) = L := by
    dsimp [v]
    rw [intervalIntegral.integral_add ((hEi l r).const_mul speed)
      (((continuous_const.intervalIntegrable l r).sub (hEi l r)).const_mul B)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (continuous_const.intervalIntegrable l r) (hEi l r)]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    change speed * I + B * (r - l - I) = L
    linarith
  have ha1 : a r = 2 * Real.pi - theta0 := by rw [ha, hval]; dsimp [L]; ring
  have haDiff (x t : ℝ) : a t = a x + ∫ s in x..t, v s := by
    rw [ha t, ha x]
    have hi := intervalIntegral.integral_add_adjacent_intervals (hvi l x) (hvi x t)
    linarith
  have haAffine (x t : ℝ) (ht : t ∈ Icc (x - eta) (x + eta))
      (hx : ∀ s ∈ Icc (x - eta) (x + eta), E s = 1) :
      a t = a x + speed * (t - x) := by
    rw [haDiff x t, hconstIntegral _ _ _ speed]
    · ring
    · intro s hs
      have hs' : s ∈ Icc (x - eta) (x + eta) := by
        rcases le_total x t with hxt | htx
        · rw [uIcc_of_le hxt] at hs
          exact ⟨by linarith [hs.1], hs.2.trans ht.2⟩
        · rw [uIcc_of_ge htx] at hs
          exact ⟨ht.1.trans hs.1, by linarith [hs.2]⟩
      dsimp [v]
      rw [hx s hs']
      ring
  have hal (t : ℝ) (ht : t ∈ Icc (l - eta) (l + eta)) :
      a t = theta0 + speed * (t - l) := by rw [haAffine l t ht hEl, ha0]
  have har (t : ℝ) (ht : t ∈ Icc (r - eta) (r + eta)) :
      a t = 2 * Real.pi - theta0 + speed * (t - r) := by rw [haAffine r t ht hEr, ha1]
  let rho : ℝ → ℝ := cut 0 (e / 2)
  have hrho : ContDiff ℝ ∞ rho := hcutSmooth 0 (e / 2)
  have hrhoi (x y : ℝ) : IntervalIntegrable rho volume x y := hrho.continuous.intervalIntegrable x y
  have hrho0 (t : ℝ) : 0 ≤ rho t := (hcutBounds 0 (e / 2) t).1
  have hrhoZero (t : ℝ) (ht : t ≤ -e ∨ e ≤ t) : rho t = 0 := by
    apply hcutZero 0 (e / 2) t (by positivity)
    rcases ht with ht | ht
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hrhoAt0 : rho 0 = 1 := hcutOne 0 (e / 2) 0 (by positivity) ⟨by linarith, by linarith⟩
  let J : ℝ := ∫ t in (-theta0)..theta0, rho t
  have hJ : 0 < J := intervalIntegral.integral_pos (by linarith)
    hrho.continuous.continuousOn (fun t _ => hrho0 t)
    ⟨0, ⟨by linarith, ht0pos.le⟩, by rw [hrhoAt0]; norm_num⟩
  let D : ℝ := (1 - 2 * theta0 / speed) / J
  have hD : 0 < D := div_pos (by
    have hi : 2 * theta0 / speed < 1 := (div_lt_one hspos).mpr hslarge
    linarith) hJ
  have hDJ : D * J = 1 - 2 * theta0 / speed := div_mul_cancel₀ _ hJ.ne'
  let w : ℝ → ℝ := fun t => 1 / speed + D * rho t
  have hw : ContDiff ℝ ∞ w := contDiff_const.add (contDiff_const.mul hrho)
  have hwi (x y : ℝ) : IntervalIntegrable w volume x y := hw.continuous.intervalIntegrable x y
  have hwm (t : ℝ) : 1 / speed ≤ w t := by
    dsimp [w]
    exact le_add_of_nonneg_right (mul_nonneg hD.le (hrho0 t))
  obtain ⟨b, hb, hbm, hbd⟩ := hprimitive w hw (1 / speed) (by positivity) hwm (-theta0) 0
  have hb0 : b (-theta0) = 0 := by rw [hb]; simp
  have hwval : (∫ t in (-theta0)..theta0, w t) = 1 := by
    dsimp [w]
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      ((hrhoi _ _).const_mul D), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul]
    change (theta0 - -theta0) * (1 / speed) + D * J = 1
    rw [hDJ]
    ring
  have hb1 : b theta0 = 1 := by rw [hb, hwval]; ring
  have hbDiff (x t : ℝ) : b t = b x + ∫ s in x..t, w s := by
    rw [hb t, hb x]
    have hi := intervalIntegral.integral_add_adjacent_intervals (hwi (-theta0) x) (hwi x t)
    linarith
  have hbl (t : ℝ) (ht : t ≤ -e) : b t = (t + theta0) / speed := by
    rw [hbDiff (-theta0), hb0, hconstIntegral _ _ _ (1 / speed)]
    · ring
    · intro s hs
      have hs' : s ≤ -e := by
        rcases le_total (-theta0) t with hxt | htx
        · rw [uIcc_of_le hxt] at hs
          exact hs.2.trans ht
        · rw [uIcc_of_ge htx] at hs
          linarith [hs.2]
      simp only [w, hrhoZero s (Or.inl hs'), mul_zero, add_zero]
  have hbr (t : ℝ) (ht : e ≤ t) : b t = 1 + (t - theta0) / speed := by
    rw [hbDiff theta0, hb1, hconstIntegral _ _ _ (1 / speed)]
    · ring
    · intro s hs
      have hs' : e ≤ s := by
        rcases le_total theta0 t with hxt | htx
        · rw [uIcc_of_le hxt] at hs
          linarith [hs.1]
        · rw [uIcc_of_ge htx] at hs
          exact ht.trans hs.1
      simp only [w, hrhoZero s (Or.inr hs'), mul_zero, add_zero]
  have hae : a (l - eta) = e := by
    rw [hal _ ⟨le_rfl, by linarith⟩]
    dsimp [e]
    nlinarith [hseta]
  have haf : a (r + eta) = 2 * Real.pi - e := by
    rw [har _ ⟨by linarith, le_rfl⟩]
    dsimp [e]
    nlinarith [hseta]
  have hbMinus : b (-f) = -eta := by
    rw [hbl _ (by dsimp [f, e]; linarith)]
    apply (div_eq_iff hspos.ne').mpr
    dsimp [f]
    nlinarith [hseta]
  have hbPlus : b f = 1 + eta := by
    rw [hbr _ (by dsimp [f, e]; linarith)]
    congr 1
    apply (div_eq_iff hspos.ne').mpr
    dsimp [f]
    nlinarith [hseta]
  have haOpen : a '' Ioo (l - eta) (r + eta) = Ioo e (2 * Real.pi - e) := by
    rw [a.contDiff.continuous.image_Ioo_of_strictMono ham, hae, haf]
  have haClosed : a '' Icc l r = Icc theta0 (2 * Real.pi - theta0) := by
    rw [a.contDiff.continuous.image_Icc_of_strictMono ham, ha0, ha1]
  have haInverse : a.symm '' Ioo e (2 * Real.pi - e) = Ioo (l - eta) (r + eta) := by
    rw [← haOpen]
    exact a.toEquiv.symm_image_image _
  have hbClosed : b '' Icc (-theta0) theta0 = Icc (0 : ℝ) 1 := by
    rw [b.contDiff.continuous.image_Icc_of_strictMono hbm, hb0, hb1]
  have hbOpen : b '' Ioo (-f) f = Ioo (-eta) (1 + eta) := by
    rw [b.contDiff.continuous.image_Ioo_of_strictMono hbm, hbMinus, hbPlus]
  have hbInverse : b.symm '' Ioo (-eta) (1 + eta) = Ioo (-f) f := by
    rw [← hbOpen]
    exact b.toEquiv.symm_image_image _
  refine ⟨a, b, heta, ?_, he, he0, ht0hi, ht1f, hfpi, ham, hbm, ?_,
    ha0, ha1, hb0, hb1, hal, har, hbl, hbr, haOpen, haClosed, haInverse,
    hbClosed, hbOpen, hbInverse⟩
  · linarith
  · intro t
    rw [had t, hbd t]
    exact ⟨(lt_min hspos hB).trans_le (hvm t), (one_div_pos.mpr hspos).trans_le (hwm t)⟩

end PoincareConjecture.M25.Topology3D
