import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ShortSectorTemplates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

noncomputable def raisedReturnSign (i : Fin 2) : ℝ := ![1, -1] i

noncomputable def raisedReturnOther (i : Fin 2) : Fin 2 := Equiv.swap (0 : Fin 2) 1 i

noncomputable def raisedReturnQ (h t : ℝ) : ℝ :=
  Real.smoothTransition ((t - h) / (1 - 2 * h))

noncomputable def raisedReturnR0 (h t : ℝ) : ℝ :=
  1 + h + (2 * h - t) * (1 - Real.smoothTransition ((t - h) / h)) +
    (2 * h - (1 - t)) * (1 - Real.smoothTransition ((1 - t - h) / h))

noncomputable def raisedReturnBump (h t : ℝ) : ℝ :=
  Real.smoothTransition (8 * raisedReturnQ h t - 1) *
    Real.smoothTransition (7 - 8 * raisedReturnQ h t)

noncomputable def raisedReturnRadius (h t : ℝ) : ℝ :=
  raisedReturnR0 h t + 9 * h * raisedReturnBump h t

noncomputable def raisedReturnAngle (h t : ℝ) : ℝ :=
  3 * Real.pi / 4 + (3 * Real.pi / 2) * raisedReturnQ h t

noncomputable def raisedReturnPlanarCurve (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (h : ℝ) (inner : Fin 2) (t : ℝ) : E2 :=
  J2.symm
    (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
        Real.cos (raisedReturnAngle h t),
      raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
        Real.sin (raisedReturnAngle h t))

noncomputable def raisedReturnPhysicalCurve (kappa : OpenPartialHomeomorph E2 E2)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (h : ℝ) (inner : Fin 2) (t : ℝ) : E2 :=
  kappa (raisedReturnPlanarCurve J2 h inner t)

lemma raisedReturnSign_sq (i : Fin 2) : raisedReturnSign i ^ 2 = 1 := by
  fin_cases i <;> simp [raisedReturnSign]

lemma raisedReturnOther_sign (i : Fin 2) :
    raisedReturnSign (raisedReturnOther i) = -raisedReturnSign i := by
  fin_cases i <;> simp [raisedReturnSign, raisedReturnOther]

lemma raisedReturnQ_contDiff (h : ℝ) :
    ContDiff ℝ ∞ (raisedReturnQ h) := by
  unfold raisedReturnQ
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma raisedReturnR0_contDiff (h : ℝ) :
    ContDiff ℝ ∞ (raisedReturnR0 h) := by
  have hsL : ContDiff ℝ ∞ (fun t : ℝ =>
      Real.smoothTransition ((t - h) / h)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hsR : ContDiff ℝ ∞ (fun t : ℝ =>
      Real.smoothTransition ((1 - t - h) / h)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hcL : ContDiff ℝ ∞ (fun t : ℝ => 2 * h - t) := by fun_prop
  have hcR : ContDiff ℝ ∞ (fun t : ℝ => 2 * h - (1 - t)) := by fun_prop
  unfold raisedReturnR0
  exact ((contDiff_const.add contDiff_const).add
      (hcL.mul (contDiff_const.sub hsL))).add
    (hcR.mul (contDiff_const.sub hsR))

lemma raisedReturnBump_contDiff (h : ℝ) :
    ContDiff ℝ ∞ (raisedReturnBump h) := by
  have hq := raisedReturnQ_contDiff h
  have hL : ContDiff ℝ ∞ (fun t : ℝ => 8 * raisedReturnQ h t - 1) := by
    simpa [smul_eq_mul] using (hq.const_smul (8 : ℝ)).sub contDiff_const
  have hR : ContDiff ℝ ∞ (fun t : ℝ => 7 - 8 * raisedReturnQ h t) := by
    simpa [smul_eq_mul] using contDiff_const.sub (hq.const_smul (8 : ℝ))
  have hSL : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (8 * raisedReturnQ h t - 1)) :=
    Real.smoothTransition.contDiff.comp hL
  have hSR : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (7 - 8 * raisedReturnQ h t)) :=
    Real.smoothTransition.contDiff.comp hR
  unfold raisedReturnBump
  exact hSL.mul hSR

lemma raisedReturnRadius_contDiff (h : ℝ) :
    ContDiff ℝ ∞ (raisedReturnRadius h) := by
  unfold raisedReturnRadius
  simpa [smul_eq_mul] using
    (raisedReturnR0_contDiff h).add ((raisedReturnBump_contDiff h).const_smul (9 * h))

lemma raisedReturnAngle_contDiff (h : ℝ) :
    ContDiff ℝ ∞ (raisedReturnAngle h) := by
  unfold raisedReturnAngle
  simpa [smul_eq_mul] using
    contDiff_const.add ((raisedReturnQ_contDiff h).const_smul (3 * Real.pi / 2))

lemma raisedReturnPlanar_contDiff (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (h : ℝ) (inner : Fin 2) :
  ContDiff ℝ ∞ (raisedReturnPlanarCurve J2 h inner) := by
  have hr := raisedReturnRadius_contDiff h
  have ha := raisedReturnAngle_contDiff h
  have hc : ContDiff ℝ ∞ (fun t : ℝ => Real.cos (raisedReturnAngle h t)) :=
    Real.contDiff_cos.comp ha
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.sin (raisedReturnAngle h t)) :=
    Real.contDiff_sin.comp ha
  have hx : ContDiff ℝ ∞ (fun t : ℝ =>
      raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
        Real.cos (raisedReturnAngle h t)) := by
    simpa [smul_eq_mul] using
      (hr.const_smul (raisedReturnSign (raisedReturnOther inner))).mul hc
  have hy : ContDiff ℝ ∞ (fun t : ℝ =>
      raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
        Real.sin (raisedReturnAngle h t)) := by
    simpa [smul_eq_mul] using
      (hr.const_smul (raisedReturnSign (raisedReturnOther inner))).mul hs
  unfold raisedReturnPlanarCurve
  exact (J2.symm.contDiff.comp (hx.prodMk hy))

lemma raisedReturnQ_bounds (h t : ℝ) :
    0 ≤ raisedReturnQ h t ∧ raisedReturnQ h t ≤ 1 := by
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma raisedReturnLeft_nonneg (h : ℝ) (hh : 0 < h) (t : ℝ) :
    0 ≤ (2 * h - t) *
      (1 - Real.smoothTransition ((t - h) / h)) := by
  by_cases ht : t ≤ 2 * h
  · exact mul_nonneg (by linarith) (by linarith [Real.smoothTransition.le_one ((t - h) / h)])
  · have ha : 1 ≤ (t - h) / h := by
      apply (le_div_iff₀ hh).2
      linarith
    rw [Real.smoothTransition.one_of_one_le ha]
    simp only [sub_self, mul_zero]
    exact le_rfl

lemma raisedReturnRight_nonneg (h : ℝ) (hh : 0 < h) (t : ℝ) :
    0 ≤ (2 * h - (1 - t)) *
      (1 - Real.smoothTransition ((1 - t - h) / h)) := by
  by_cases ht : 1 - 2 * h ≤ t
  · exact mul_nonneg (by linarith) (by linarith [Real.smoothTransition.le_one ((1 - t - h) / h)])
  · have ha : 1 ≤ (1 - t - h) / h := by
      apply (le_div_iff₀ hh).2
      linarith
    rw [Real.smoothTransition.one_of_one_le ha]
    simp only [sub_self, mul_zero]
    exact le_rfl

lemma raisedReturnLeft_le (h : ℝ) (hh : 0 < h) (t : ℝ)
    (ht : t ∈ Ioo (-h / 8) (1 + h / 8)) :
    (2 * h - t) *
      (1 - Real.smoothTransition ((t - h) / h)) ≤ 17 * h / 8 := by
  by_cases ht' : t ≤ 2 * h
  · have hx : 0 ≤ 2 * h - t := by linarith
    have hy0 : 0 ≤ 1 - Real.smoothTransition ((t - h) / h) := by
      linarith [Real.smoothTransition.le_one ((t - h) / h)]
    have hy1 : 1 - Real.smoothTransition ((t - h) / h) ≤ 1 := by
      linarith [Real.smoothTransition.nonneg ((t - h) / h)]
    have hm := mul_le_mul_of_nonneg_left hy1 hx
    calc
      _ ≤ 2 * h - t := by simpa only [mul_one] using hm
      _ ≤ 17 * h / 8 := by linarith [ht.1]
  · rw [Real.smoothTransition.one_of_one_le (by
      apply (le_div_iff₀ hh).2
      linarith)]
    simp only [sub_self, mul_zero]
    positivity

lemma raisedReturnRight_le (h : ℝ) (hh : 0 < h) (t : ℝ)
    (ht : t ∈ Ioo (-h / 8) (1 + h / 8)) :
    (2 * h - (1 - t)) *
      (1 - Real.smoothTransition ((1 - t - h) / h)) ≤ 17 * h / 8 := by
  by_cases ht' : 1 - 2 * h ≤ t
  · have hx : 0 ≤ 2 * h - (1 - t) := by linarith
    have hy0 : 0 ≤ 1 - Real.smoothTransition ((1 - t - h) / h) := by
      linarith [Real.smoothTransition.le_one ((1 - t - h) / h)]
    have hy1 : 1 - Real.smoothTransition ((1 - t - h) / h) ≤ 1 := by
      linarith [Real.smoothTransition.nonneg ((1 - t - h) / h)]
    have hm := mul_le_mul_of_nonneg_left hy1 hx
    calc
      _ ≤ 2 * h - (1 - t) := by simpa only [mul_one] using hm
      _ ≤ 17 * h / 8 := by linarith [ht.2]
  · rw [Real.smoothTransition.one_of_one_le (by
      apply (le_div_iff₀ hh).2
      linarith)]
    simp only [sub_self, mul_zero]
    positivity

lemma raisedReturnLeft_le_closed (h : ℝ) (hh : 0 < h) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (2 * h - t) *
      (1 - Real.smoothTransition ((t - h) / h)) ≤ 2 * h := by
  by_cases ht' : t ≤ 2 * h
  · have hx : 0 ≤ 2 * h - t := by linarith
    have hy0 : 0 ≤ 1 - Real.smoothTransition ((t - h) / h) := by
      linarith [Real.smoothTransition.le_one ((t - h) / h)]
    have hy1 : 1 - Real.smoothTransition ((t - h) / h) ≤ 1 := by
      linarith [Real.smoothTransition.nonneg ((t - h) / h)]
    have hm := mul_le_mul_of_nonneg_left hy1 hx
    calc
      _ ≤ 2 * h - t := by simpa only [mul_one] using hm
      _ ≤ 2 * h := by linarith [ht.1]
  · rw [Real.smoothTransition.one_of_one_le (by
      apply (le_div_iff₀ hh).2
      linarith)]
    simp only [sub_self, mul_zero]
    positivity

lemma raisedReturnRight_le_closed (h : ℝ) (hh : 0 < h) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (2 * h - (1 - t)) *
      (1 - Real.smoothTransition ((1 - t - h) / h)) ≤ 2 * h := by
  by_cases ht' : 1 - 2 * h ≤ t
  · have hx : 0 ≤ 2 * h - (1 - t) := by linarith
    have hy0 : 0 ≤ 1 - Real.smoothTransition ((1 - t - h) / h) := by
      linarith [Real.smoothTransition.le_one ((1 - t - h) / h)]
    have hy1 : 1 - Real.smoothTransition ((1 - t - h) / h) ≤ 1 := by
      linarith [Real.smoothTransition.nonneg ((1 - t - h) / h)]
    have hm := mul_le_mul_of_nonneg_left hy1 hx
    calc
      _ ≤ 2 * h - (1 - t) := by simpa only [mul_one] using hm
      _ ≤ 2 * h := by linarith [ht.2]
  · rw [Real.smoothTransition.one_of_one_le (by
      apply (le_div_iff₀ hh).2
      linarith)]
    simp only [sub_self, mul_zero]
    positivity

lemma raisedReturnRadius_nonneg (h : ℝ) (hh : 0 < h) (t : ℝ) :
    0 ≤ raisedReturnRadius h t := by
  unfold raisedReturnRadius raisedReturnR0 raisedReturnBump
  have hq := raisedReturnQ_bounds h t
  have hL := raisedReturnLeft_nonneg h hh t
  have hR := raisedReturnRight_nonneg h hh t
  have hb0 : 0 ≤ Real.smoothTransition (8 * raisedReturnQ h t - 1) :=
    Real.smoothTransition.nonneg _
  have hb1 : 0 ≤ Real.smoothTransition (7 - 8 * raisedReturnQ h t) :=
    Real.smoothTransition.nonneg _
  have hb : 0 ≤ 9 * h *
      (Real.smoothTransition (8 * raisedReturnQ h t - 1) *
        Real.smoothTransition (7 - 8 * raisedReturnQ h t)) := by
    positivity
  nlinarith

lemma raisedReturnRadius_lower (h : ℝ) (hh : 0 < h) (t : ℝ) :
    1 + h ≤ raisedReturnRadius h t := by
  unfold raisedReturnRadius raisedReturnR0 raisedReturnBump
  have hL := raisedReturnLeft_nonneg h hh t
  have hR := raisedReturnRight_nonneg h hh t
  have hb0 : 0 ≤ Real.smoothTransition (8 * raisedReturnQ h t - 1) :=
    Real.smoothTransition.nonneg _
  have hb1 : 0 ≤ Real.smoothTransition (7 - 8 * raisedReturnQ h t) :=
    Real.smoothTransition.nonneg _
  have hb : 0 ≤ 9 * h *
      (Real.smoothTransition (8 * raisedReturnQ h t - 1) *
        Real.smoothTransition (7 - 8 * raisedReturnQ h t)) := by
    positivity
  nlinarith

lemma raisedReturnRadius_upper_open (h : ℝ) (hh : 0 < h)
    (hsmall : h < 1 / 1024) (t : ℝ)
    (ht : t ∈ Ioo (-h / 8) (1 + h / 8)) :
    raisedReturnRadius h t < 2 := by
  unfold raisedReturnRadius raisedReturnR0 raisedReturnBump
  have hL := raisedReturnLeft_le h hh t ht
  have hR := raisedReturnRight_le h hh t ht
  have hb0 : 0 ≤ Real.smoothTransition (8 * raisedReturnQ h t - 1) :=
    Real.smoothTransition.nonneg _
  have hb1 : 0 ≤ Real.smoothTransition (7 - 8 * raisedReturnQ h t) :=
    Real.smoothTransition.nonneg _
  have hb0' : Real.smoothTransition (8 * raisedReturnQ h t - 1) ≤ 1 :=
    Real.smoothTransition.le_one _
  have hb1' : Real.smoothTransition (7 - 8 * raisedReturnQ h t) ≤ 1 :=
    Real.smoothTransition.le_one _
  have hb : Real.smoothTransition (8 * raisedReturnQ h t - 1) *
      Real.smoothTransition (7 - 8 * raisedReturnQ h t) ≤ 1 := by
    calc
      _ ≤ 1 * Real.smoothTransition (7 - 8 * raisedReturnQ h t) :=
        mul_le_mul_of_nonneg_right hb0' hb1
      _ ≤ 1 := by simpa only [one_mul] using hb1'
  nlinarith

lemma raisedReturnLeft_le_middle (h : ℝ) (hh : 0 < h) (t : ℝ)
    (ht : h ≤ t) :
    (2 * h - t) *
      (1 - Real.smoothTransition ((t - h) / h)) ≤ h := by
  by_cases ht' : t ≤ 2 * h
  · have hx : 0 ≤ 2 * h - t := by linarith
    have hy : 1 - Real.smoothTransition ((t - h) / h) ≤ 1 := by
      linarith [Real.smoothTransition.nonneg ((t - h) / h)]
    have hm := mul_le_mul_of_nonneg_left hy hx
    calc
      _ ≤ 2 * h - t := by simpa only [mul_one] using hm
      _ ≤ h := by linarith
  · rw [Real.smoothTransition.one_of_one_le (by
      apply (le_div_iff₀ hh).2
      linarith)]
    simp only [sub_self, mul_zero]
    exact hh.le

lemma raisedReturnRight_le_middle (h : ℝ) (hh : 0 < h) (t : ℝ)
    (ht : t ≤ 1 - h) :
    (2 * h - (1 - t)) *
      (1 - Real.smoothTransition ((1 - t - h) / h)) ≤ h := by
  by_cases ht' : 1 - 2 * h ≤ t
  · have hx : 0 ≤ 2 * h - (1 - t) := by linarith
    have hy : 1 - Real.smoothTransition ((1 - t - h) / h) ≤ 1 := by
      linarith [Real.smoothTransition.nonneg ((1 - t - h) / h)]
    have hm := mul_le_mul_of_nonneg_left hy hx
    calc
      _ ≤ 2 * h - (1 - t) := by simpa only [mul_one] using hm
      _ ≤ h := by linarith
  · rw [Real.smoothTransition.one_of_one_le (by
      apply (le_div_iff₀ hh).2
      linarith)]
    simp only [sub_self, mul_zero]
    exact hh.le

lemma raisedReturnRadius_upper_closed (h : ℝ) (hh : 0 < h)
    (hsmall : h < 1 / 1024) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    raisedReturnRadius h t ≤ 1 + 11 * h := by
  have hL := raisedReturnLeft_le_closed h hh t ht
  have hR := raisedReturnRight_le_closed h hh t ht
  have hb0 : 0 ≤ Real.smoothTransition (8 * raisedReturnQ h t - 1) :=
    Real.smoothTransition.nonneg _
  have hb1 : 0 ≤ Real.smoothTransition (7 - 8 * raisedReturnQ h t) :=
    Real.smoothTransition.nonneg _
  have hb_le : raisedReturnBump h t ≤ 1 := by
    unfold raisedReturnBump
    have h0 : Real.smoothTransition (8 * raisedReturnQ h t - 1) ≤ 1 :=
      Real.smoothTransition.le_one _
    have h1 : Real.smoothTransition (7 - 8 * raisedReturnQ h t) ≤ 1 :=
      Real.smoothTransition.le_one _
    calc
      _ ≤ 1 * Real.smoothTransition (7 - 8 * raisedReturnQ h t) :=
        mul_le_mul_of_nonneg_right h0 hb1
      _ ≤ 1 := by simpa only [one_mul] using h1
  by_cases hb : raisedReturnBump h t = 0
  · unfold raisedReturnRadius raisedReturnR0
    rw [hb]
    nlinarith
  · have hbpos : 0 < raisedReturnBump h t := by
      exact lt_of_le_of_ne (mul_nonneg hb0 hb1) (Ne.symm hb)
    have hqL : (1 / 8 : ℝ) < raisedReturnQ h t := by
      have hf := pos_of_mul_pos_left hbpos hb1
      have hz : 0 < 8 * raisedReturnQ h t - 1 := by
        by_contra hnot
        have hz' : 8 * raisedReturnQ h t - 1 ≤ 0 := le_of_not_gt hnot
        rw [Real.smoothTransition.zero_of_nonpos hz'] at hf
        exact (lt_irrefl 0) hf
      linarith
    have hqR : raisedReturnQ h t < (7 / 8 : ℝ) := by
      have hf := pos_of_mul_pos_right hbpos hb0
      have hz : 0 < 7 - 8 * raisedReturnQ h t := by
        by_contra hnot
        have hz' : 7 - 8 * raisedReturnQ h t ≤ 0 := not_lt.mp hnot
        rw [Real.smoothTransition.zero_of_nonpos hz'] at hf
        linarith
      linarith
    have hd : 0 < 1 - 2 * h := by linarith
    have hqpos : 0 < raisedReturnQ h t := by linarith
    have hqone : raisedReturnQ h t < 1 := by linarith
    have hzpos : 0 < (t - h) / (1 - 2 * h) := by
      unfold raisedReturnQ at hqpos
      by_contra hnot
      have hz : (t - h) / (1 - 2 * h) ≤ 0 := le_of_not_gt hnot
      rw [Real.smoothTransition.zero_of_nonpos hz] at hqpos
      exact (lt_irrefl 0) hqpos
    have hzone : (t - h) / (1 - 2 * h) < 1 := by
      unfold raisedReturnQ at hqone
      by_contra hnot
      have hz : 1 ≤ (t - h) / (1 - 2 * h) := le_of_not_gt hnot
      rw [Real.smoothTransition.one_of_one_le hz] at hqone
      exact (lt_irrefl 1) hqone
    have htmid : h < t ∧ t < 1 - h := by
      constructor
      · have := (div_pos_iff.mp hzpos)
        rcases this with hpos | hneg
        · linarith
        · exact False.elim (by linarith)
      · have := (div_lt_iff₀ hd).mp hzone
        linarith
    have hbprod : Real.smoothTransition (8 * raisedReturnQ h t - 1) *
        Real.smoothTransition (7 - 8 * raisedReturnQ h t) ≤ 1 := by
      simpa [raisedReturnBump] using hb_le
    have hbterm : 9 * h *
        (Real.smoothTransition (8 * raisedReturnQ h t - 1) *
          Real.smoothTransition (7 - 8 * raisedReturnQ h t)) ≤ 9 * h := by
      have h9 : 0 ≤ (9 : ℝ) * h := by positivity
      calc
        _ = (9 * h) *
            (Real.smoothTransition (8 * raisedReturnQ h t - 1) *
              Real.smoothTransition (7 - 8 * raisedReturnQ h t)) := by ring
        _ ≤ (9 * h) * 1 := mul_le_mul_of_nonneg_left hbprod h9
        _ = 9 * h := by ring
    by_cases htHalf : t ≤ 1 / 2
    · have hRzero : (2 * h - (1 - t)) *
          (1 - Real.smoothTransition ((1 - t - h) / h)) = 0 := by
        have hsone : Real.smoothTransition ((1 - t - h) / h) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          apply (le_div_iff₀ hh).2
          linarith [htHalf, hsmall]
        rw [hsone]
        ring
      have hLm := raisedReturnLeft_le_middle h hh t htmid.1.le
      unfold raisedReturnRadius raisedReturnR0
      rw [hRzero]
      rw [show raisedReturnBump h t =
        Real.smoothTransition (8 * raisedReturnQ h t - 1) *
          Real.smoothTransition (7 - 8 * raisedReturnQ h t) by rfl]
      nlinarith [hLm, hbterm]
    · have htHalf' : 1 / 2 < t := lt_of_not_ge htHalf
      have hLzero : (2 * h - t) *
          (1 - Real.smoothTransition ((t - h) / h)) = 0 := by
        have hsone : Real.smoothTransition ((t - h) / h) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          apply (le_div_iff₀ hh).2
          linarith [htHalf', hsmall]
        rw [hsone]
        ring
      have hRm := raisedReturnRight_le_middle h hh t htmid.2.le
      unfold raisedReturnRadius raisedReturnR0
      rw [hLzero]
      rw [show raisedReturnBump h t =
        Real.smoothTransition (8 * raisedReturnQ h t - 1) *
          Real.smoothTransition (7 - 8 * raisedReturnQ h t) by rfl]
      nlinarith [hRm, hbterm]

lemma raisedReturnPlanar_norm_eq_radius
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (inner : Fin 2) (t : ℝ)
    (hR : 0 ≤ raisedReturnRadius h t) :
    ‖raisedReturnPlanarCurve J2 h inner t‖ = raisedReturnRadius h t := by
  have he := hJ2 (raisedReturnPlanarCurve J2 h inner t)
  rw [show J2 (raisedReturnPlanarCurve J2 h inner t) =
      (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
          Real.cos (raisedReturnAngle h t),
       raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
          Real.sin (raisedReturnAngle h t)) by
        simp [raisedReturnPlanarCurve]] at he
  change
    (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
        Real.cos (raisedReturnAngle h t)) ^ 2 +
      (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
        Real.sin (raisedReturnAngle h t)) ^ 2 =
      ‖raisedReturnPlanarCurve J2 h inner t‖ ^ 2 at he
  have hs := raisedReturnSign_sq (raisedReturnOther inner)
  have he' : ‖raisedReturnPlanarCurve J2 h inner t‖ ^ 2 =
      raisedReturnRadius h t ^ 2 := by
    calc
      ‖raisedReturnPlanarCurve J2 h inner t‖ ^ 2 =
          (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
            Real.cos (raisedReturnAngle h t)) ^ 2 +
            (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h t *
              Real.sin (raisedReturnAngle h t)) ^ 2 := he.symm
      _ = raisedReturnRadius h t ^ 2 := by
        calc
          _ = raisedReturnRadius h t ^ 2 *
              (Real.cos (raisedReturnAngle h t) ^ 2 +
                Real.sin (raisedReturnAngle h t) ^ 2) := by
                nlinarith [hs]
          _ = raisedReturnRadius h t ^ 2 := by
            rw [Real.cos_sq_add_sin_sq]
            ring
  nlinarith [norm_nonneg (raisedReturnPlanarCurve J2 h inner t)]

lemma raisedReturn_q_zero_left (h : ℝ) (hh : 0 < h)
    (hsmall : h < 1 / 1024) (t : ℝ) (ht : t ≤ h) :
    raisedReturnQ h t = 0 := by
  unfold raisedReturnQ
  apply Real.smoothTransition.zero_of_nonpos
  have hd : 0 < 1 - 2 * h := by linarith
  apply div_nonpos_iff.mpr
  exact Or.inr ⟨by linarith, hd.le⟩

lemma raisedReturn_q_one_right (h : ℝ) (hh : 0 < h)
    (hsmall : h < 1 / 1024) (t : ℝ) (ht : 1 - h ≤ t) :
    raisedReturnQ h t = 1 := by
  unfold raisedReturnQ
  apply Real.smoothTransition.one_of_one_le
  have hd : 0 < 1 - 2 * h := by linarith
  apply (le_div_iff₀ hd).2
  linarith

lemma raisedReturn_left_formula (h : ℝ) (hh : 0 < h)
    (hsmall : h < 1 / 1024) (t : ℝ) (ht : t ≤ h) :
    raisedReturnRadius h t = 1 + 3 * h - t := by
  have hq := raisedReturn_q_zero_left h hh hsmall t ht
  have hsl : Real.smoothTransition ((t - h) / h) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by
      apply div_nonpos_iff.mpr
      exact Or.inr ⟨by linarith, le_of_lt hh⟩)
  have hsr : Real.smoothTransition ((1 - t - h) / h) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hh).2
    linarith
  have hb : raisedReturnBump h t = 0 := by
    unfold raisedReturnBump
    rw [hq]
    norm_num only [mul_zero, sub_zero, mul_one, sub_self, one_mul]
    have hz : Real.smoothTransition (-1 : ℝ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by norm_num)
    rw [hz]
    simp
  simp [raisedReturnRadius, raisedReturnR0, hsl, hsr, hb]
  ring

lemma raisedReturn_right_formula (h : ℝ) (hh : 0 < h)
    (hsmall : h < 1 / 1024) (t : ℝ) (ht : 1 - h ≤ t) :
    raisedReturnRadius h t = 1 + 3 * h + t - 1 := by
  have hq := raisedReturn_q_one_right h hh hsmall t ht
  have hsl : Real.smoothTransition ((t - h) / h) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hh).2
    linarith
  have hsr : Real.smoothTransition ((1 - t - h) / h) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by
      apply div_nonpos_iff.mpr
      exact Or.inr ⟨by linarith, le_of_lt hh⟩)
  have hb : raisedReturnBump h t = 0 := by
    unfold raisedReturnBump
    rw [hq]
    norm_num only [mul_zero, sub_zero, mul_one, sub_self, one_mul]
    have hz : Real.smoothTransition (-1 : ℝ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by norm_num)
    rw [hz]
    simp
  simp [raisedReturnRadius, raisedReturnR0, hsl, hsr, hb]
  ring

lemma raisedReturn_q_mid (h : ℝ) (hsmall : h < 1 / 1024) :
    raisedReturnQ h (1 / 2) = 1 / 2 := by
  have hhalf : Real.smoothTransition (1 / 2 : ℝ) = 1 / 2 := by
    dsimp only [Real.smoothTransition]
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    have hn := (expNegInvGlue.pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)).ne'
    field_simp [hn]
    ring
  unfold raisedReturnQ
  have hd : 1 - 2 * h ≠ 0 := by linarith
  rw [show ((1 / 2 : ℝ) - h) / (1 - 2 * h) = 1 / 2 by field_simp [hd], hhalf]

lemma raisedReturn_mid_formula (h : ℝ) (hh : 0 < h)
    (hsmall : h < 1 / 1024) (J2 : E2 ≃L[ℝ] (ℝ × ℝ)) (inner : Fin 2) :
    raisedReturnPlanarCurve J2 h inner (1 / 2) =
      J2.symm (0, raisedReturnSign inner * (1 + 10 * h)) := by
  have hq := raisedReturn_q_mid h hsmall
  have hsL : Real.smoothTransition (((1 / 2 : ℝ) - h) / h) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hh).2
    linarith
  have hsR : Real.smoothTransition ((1 - (1 / 2 : ℝ) - h) / h) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hh).2
    linarith
  have hb : raisedReturnBump h (1 / 2) = 1 := by
    unfold raisedReturnBump
    rw [hq]
    norm_num [Real.smoothTransition.one_of_one_le]
  have hr : raisedReturnRadius h (1 / 2) = 1 + 10 * h := by
    have hr0 : raisedReturnR0 h (1 / 2) = 1 + h := by
      unfold raisedReturnR0
      rw [hsL, hsR]
      ring
    rw [raisedReturnRadius, hr0, hb]
    ring
  have ha : raisedReturnAngle h (1 / 2) = 3 * Real.pi / 2 := by
    unfold raisedReturnAngle
    rw [hq]
    ring
  rw [raisedReturnPlanarCurve, hr, ha]
  have htrig : Real.cos (3 * Real.pi / 2) = 0 ∧
      Real.sin (3 * Real.pi / 2) = -1 := by
    rw [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    norm_num
  rw [htrig.1, htrig.2]
  simp only [mul_zero, mul_neg, mul_one]
  rw [raisedReturnOther_sign]
  ring

lemma raisedReturn_opposite_sector_q
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (h : ℝ) (hh : 0 < h) (_hsmall : h < 1 / 1024)
    (inner : Fin 2) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
    (hsector : |(J2 (raisedReturnPlanarCurve J2 h inner t)).1| ≤
      raisedReturnSign inner * (J2 (raisedReturnPlanarCurve J2 h inner t)).2) :
    raisedReturnQ h t ∈ Icc (1 / 3 : ℝ) (2 / 3) := by
  have hR : 0 < raisedReturnRadius h t :=
    lt_of_lt_of_le (by linarith) (raisedReturnRadius_lower h hh t)
  have hpolar : |Real.cos (raisedReturnAngle h t)| ≤
      -Real.sin (raisedReturnAngle h t) := by
    have hmul : raisedReturnRadius h t *
        |Real.cos (raisedReturnAngle h t)| ≤
        raisedReturnRadius h t * (-Real.sin (raisedReturnAngle h t)) := by
      fin_cases inner <;>
        simpa [raisedReturnPlanarCurve, raisedReturnSign, raisedReturnOther,
          abs_mul, abs_of_pos hR, neg_mul] using hsector
    exact le_of_mul_le_mul_left hmul hR
  have hq := raisedReturnQ_bounds h t
  have hangle_low : 3 * Real.pi / 4 ≤ raisedReturnAngle h t := by
    unfold raisedReturnAngle
    nlinarith [hq.1, Real.pi_pos]
  have hangle_high : raisedReturnAngle h t ≤ 9 * Real.pi / 4 := by
    unfold raisedReturnAngle
    nlinarith [hq.2, Real.pi_pos]
  have hq_low : (1 / 3 : ℝ) ≤ raisedReturnQ h t := by
    by_contra hnot
    have hq_lt : raisedReturnQ h t < 1 / 3 := lt_of_not_ge hnot
    have hangle_lt : raisedReturnAngle h t < 5 * Real.pi / 4 := by
      unfold raisedReturnAngle
      nlinarith [hq_lt, Real.pi_pos]
    by_cases hapi : raisedReturnAngle h t ≤ Real.pi
    · have hs : 0 ≤ Real.sin (raisedReturnAngle h t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hangle_low]) hapi
      have hc : Real.cos (raisedReturnAngle h t) = 0 := by
        apply abs_eq_zero.mp
        nlinarith [abs_nonneg (Real.cos (raisedReturnAngle h t))]
      have hs0 : Real.sin (raisedReturnAngle h t) = 0 := by
        rw [hc, abs_zero] at hpolar
        nlinarith [hpolar]
      nlinarith [Real.sin_sq_add_cos_sq (raisedReturnAngle h t)]
    · have hapi' : Real.pi < raisedReturnAngle h t := lt_of_not_ge hapi
      have hc : Real.cos (raisedReturnAngle h t) ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [Real.pi_pos])
          (by linarith [hangle_lt])
      have hdiff : 0 < Real.sin (raisedReturnAngle h t) -
          Real.cos (raisedReturnAngle h t) := by
        have hs : 0 < Real.sin (raisedReturnAngle h t - Real.pi / 4) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hapi', Real.pi_pos])
            (by linarith [hangle_lt, Real.pi_pos])
        rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four] at hs
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
      rw [abs_of_nonpos hc] at hpolar
      linarith
  have hq_high : raisedReturnQ h t ≤ (2 / 3 : ℝ) := by
    by_contra hnot
    have hq_gt : (2 / 3 : ℝ) < raisedReturnQ h t := lt_of_not_ge hnot
    have hangle_gt : 7 * Real.pi / 4 < raisedReturnAngle h t := by
      unfold raisedReturnAngle
      nlinarith [hq_gt, Real.pi_pos]
    have hc : 0 ≤ Real.cos (raisedReturnAngle h t) := by
      rw [← Real.cos_sub_two_pi]
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [hangle_gt, hangle_high]
    have hsplus : 0 < Real.sin (raisedReturnAngle h t) +
        Real.cos (raisedReturnAngle h t) := by
      have hs : 0 < Real.sin (raisedReturnAngle h t + Real.pi / 4) := by
        rw [show raisedReturnAngle h t + Real.pi / 4 =
          (raisedReturnAngle h t - 7 * Real.pi / 4) + 2 * Real.pi by ring,
          Real.sin_add_two_pi]
        apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hangle_gt, hangle_high]
      rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four] at hs
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    rw [abs_of_nonneg hc] at hpolar
    linarith
  exact ⟨hq_low, hq_high⟩

lemma raisedReturn_bump_eq_one_of_opposite_sector
    (h : ℝ) (t : ℝ)
    (hq : raisedReturnQ h t ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    raisedReturnBump h t = 1 := by
  unfold raisedReturnBump
  rw [Real.smoothTransition.one_of_one_le (by linarith [hq.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hq.2])]
  norm_num

lemma raisedReturn_radius_lower_of_opposite_sector
    (h : ℝ) (hh : 0 < h) (t : ℝ)
    (hq : raisedReturnQ h t ∈ Icc (1 / 3 : ℝ) (2 / 3)) :
    1 + 10 * h ≤ raisedReturnRadius h t := by
  have hL := raisedReturnLeft_nonneg h hh t
  have hR := raisedReturnRight_nonneg h hh t
  have hb := raisedReturn_bump_eq_one_of_opposite_sector h t hq
  unfold raisedReturnRadius raisedReturnR0 at *
  rw [hb]
  nlinarith

end PoincareConjecture.M25.Topology3D
