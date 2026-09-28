import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorTemplatesScalar
import PoincareConjecture.Proofs.M25.Mathlib.PolarCurve

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

theorem exists_saddle_nested_raised_long_return
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024)
    (inner : Fin 2) (beta : ℝ → E2)
    (hbeta : Set.MapsTo beta (Icc (0 : ℝ) 1)
      (kappa '' {x : E2 |
        1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 6 * h ∧
          |(J2 x).1| ≤ raisedReturnSign inner * (J2 x).2})) :
    ∃ g gamma : ℝ → E2,
      g = raisedReturnPlanarCurve J2 h inner ∧
      gamma = raisedReturnPhysicalCurve kappa J2 h inner ∧
      ContDiff ℝ ∞ g ∧
      ContDiffOn ℝ ∞ gamma (Ioo (-h / 8) (1 + h / 8)) ∧
      Set.InjOn g (Ioo (-h / 8) (1 + h / 8)) ∧
      Set.InjOn gamma (Ioo (-h / 8) (1 + h / 8)) ∧
      (∀ t ∈ Ioo (-h / 8) (1 + h / 8),
        deriv g t ≠ 0 ∧ deriv gamma t ≠ 0) ∧
      (∀ t, gamma t = kappa (g t)) ∧
      (∀ t ∈ Ioo (-h / 8) (1 + h / 8),
        g t ∈ kappa.source ∧ 1 < ‖g t‖ ∧ ‖g t‖ < 2) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        1 + h ≤ ‖g t‖ ∧ ‖g t‖ ≤ 1 + 11 * h) ∧
      g (1 / 2) = J2.symm (0, raisedReturnSign inner * (1 + 10 * h)) ∧
      (∀ t ∈ Ioo (-h / 8) (1 + h / 8), t ≤ h →
        gamma t = kappa (J2.symm
          (raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h - t) *
              Real.cos (3 * Real.pi / 4),
            raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h - t) *
              Real.sin (3 * Real.pi / 4)))) ∧
      (∀ t ∈ Ioo (-h / 8) (1 + h / 8), 1 - h ≤ t →
        gamma t = kappa (J2.symm
          (raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h + t - 1) *
              Real.cos (9 * Real.pi / 4),
            raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h + t - 1) *
              Real.sin (9 * Real.pi / 4)))) ∧
      MapsTo beta (Icc (0 : ℝ) 1)
        (kappa '' {x : E2 |
          1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 6 * h ∧
            |(J2 x).1| ≤ raisedReturnSign inner * (J2 x).2}) ∧
      Disjoint (gamma '' Icc (0 : ℝ) 1) (beta '' Icc (0 : ℝ) 1) := by
  have hcurveSmooth : ContDiff ℝ ∞ (raisedReturnPlanarCurve J2 h inner) :=
    raisedReturnPlanar_contDiff J2 h inner
  have hcurveNorm (t : ℝ) :
      ‖raisedReturnPlanarCurve J2 h inner t‖ = raisedReturnRadius h t :=
    raisedReturnPlanar_norm_eq_radius J2 hJ2 h inner t
      (raisedReturnRadius_nonneg h hh t)
  have hsource : ∀ t ∈ Ioo (-h / 8) (1 + h / 8),
      raisedReturnPlanarCurve J2 h inner t ∈ kappa.source := by
    intro t ht
    apply hkappaSource
    rw [mem_closedBall_zero_iff, hcurveNorm t]
    exact (raisedReturnRadius_upper_open h hh hsmall t ht).le
  have hbuffer : ∀ t ∈ Ioo (-h / 8) (1 + h / 8),
      1 < ‖raisedReturnPlanarCurve J2 h inner t‖ ∧
        ‖raisedReturnPlanarCurve J2 h inner t‖ < 2 := by
    intro t ht
    rw [hcurveNorm t]
    exact ⟨lt_of_lt_of_le (by linarith) (raisedReturnRadius_lower h hh t),
      raisedReturnRadius_upper_open h hh hsmall t ht⟩
  have hphysicalSmooth : ContDiffOn ℝ ∞
      (raisedReturnPhysicalCurve kappa J2 h inner)
      (Ioo (-h / 8) (1 + h / 8)) := by
    exact hkappa.comp hcurveSmooth.contDiffOn hsource
  have hradius : ∀ t ∈ Icc (0 : ℝ) 1,
      1 + h ≤ ‖raisedReturnPlanarCurve J2 h inner t‖ ∧
        ‖raisedReturnPlanarCurve J2 h inner t‖ ≤ 1 + 11 * h := by
    intro t ht
    rw [hcurveNorm t]
    exact ⟨raisedReturnRadius_lower h hh t,
      raisedReturnRadius_upper_closed h hh hsmall t ht⟩
  have hleftD (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a c v : ℝ)
      (he : ∀ t ≤ a, f t = c + v * t) (t : ℝ) (ht : t ≤ a) :
      deriv f t = v := by
    have hl : HasDerivAt (fun s : ℝ => c + v * s) v t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul v).const_add c
    exact (uniqueDiffOn_Iic a t ht).eq_deriv _
      ((hf.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt)
      (hl.hasDerivWithinAt.congr_of_mem he ht)
  have hrightD (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a c v : ℝ)
      (he : ∀ t, a ≤ t → f t = c + v * t) (t : ℝ) (ht : a ≤ t) :
      deriv f t = v := by
    have hl : HasDerivAt (fun s : ℝ => c + v * s) v t := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id t).const_mul v).const_add c
    exact (uniqueDiffOn_Ici a t ht).eq_deriv _
      ((hf.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt)
      (hl.hasDerivWithinAt.congr_of_mem he ht)
  have hpairHasDeriv (t : ℝ) :
      HasDerivAt
        (fun s : ℝ =>
          (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s),
            raisedReturnRadius h s * Real.sin (raisedReturnAngle h s)))
        ( (deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t) +
              raisedReturnRadius h t *
                (-Real.sin (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t)),
          (deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t) +
              raisedReturnRadius h t *
                (Real.cos (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t)) ) t := by
    have hr := (raisedReturnRadius_contDiff h).differentiable (by simp) t |>.hasDerivAt
    have ha := (raisedReturnAngle_contDiff h).differentiable (by simp) t |>.hasDerivAt
    convert! (hr.mul ha.cos).prodMk (hr.mul ha.sin) using 1
  have hplanarRegular_of_pair (t : ℝ)
      (hp : deriv (fun s : ℝ =>
        (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s),
          raisedReturnRadius h s * Real.sin (raisedReturnAngle h s))) t ≠ 0) :
      deriv (raisedReturnPlanarCurve J2 h inner) t ≠ 0 := by
    have hso : raisedReturnSign (raisedReturnOther inner) ≠ 0 := by
      intro hz
      have hs := raisedReturnSign_sq (raisedReturnOther inner)
      rw [hz] at hs
      norm_num at hs
    have hsigned : HasDerivAt
        (fun s : ℝ =>
          (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h s *
              Real.cos (raisedReturnAngle h s),
            raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h s *
              Real.sin (raisedReturnAngle h s)))
        (raisedReturnSign (raisedReturnOther inner) *
            (deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t) +
              raisedReturnRadius h t *
                (-Real.sin (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t)),
          raisedReturnSign (raisedReturnOther inner) *
            (deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t) +
              raisedReturnRadius h t *
                (Real.cos (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t))) t := by
      have hr := (raisedReturnRadius_contDiff h).differentiable (by simp) t |>.hasDerivAt
      have ha := (raisedReturnAngle_contDiff h).differentiable (by simp) t |>.hasDerivAt
      convert! (((hr.const_mul (raisedReturnSign (raisedReturnOther inner))).mul ha.cos).prodMk
        ((hr.const_mul (raisedReturnSign (raisedReturnOther inner))).mul ha.sin)) using 1
      apply Prod.ext <;> ring
    have hd : HasDerivAt (raisedReturnPlanarCurve J2 h inner)
        (J2.symm
          (raisedReturnSign (raisedReturnOther inner) *
              (deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t) +
                raisedReturnRadius h t *
                  (-Real.sin (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t)),
            raisedReturnSign (raisedReturnOther inner) *
              (deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t) +
                raisedReturnRadius h t *
                  (Real.cos (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t)))) t := by
      change HasDerivAt
        (fun s : ℝ => J2.symm
          (raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h s *
              Real.cos (raisedReturnAngle h s),
            raisedReturnSign (raisedReturnOther inner) * raisedReturnRadius h s *
              Real.sin (raisedReturnAngle h s))) _ t
      exact (J2.symm : (ℝ × ℝ) →L[ℝ] E2).hasFDerivAt.comp_hasDerivAt t hsigned
    intro hz
    rw [hd.deriv] at hz
    have hz' := congrArg J2 hz
    simp only [J2.apply_symm_apply, map_zero] at hz'
    have hx := congrArg Prod.fst hz'
    have hy := congrArg Prod.snd hz'
    have hx' : raisedReturnSign (raisedReturnOther inner) *
        (deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t) +
          raisedReturnRadius h t *
            (-Real.sin (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t)) = 0 := by
      simpa using hx
    have hy' : raisedReturnSign (raisedReturnOther inner) *
        (deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t) +
          raisedReturnRadius h t *
            (Real.cos (raisedReturnAngle h t) * deriv (raisedReturnAngle h) t)) = 0 := by
      simpa using hy
    apply hp
    rw [(hpairHasDeriv t).deriv]
    apply Prod.ext
    · exact (mul_eq_zero.mp hx').resolve_left hso
    · exact (mul_eq_zero.mp hy').resolve_left hso
  have hcurveRegular : ∀ t ∈ Ioo (-h / 8) (1 + h / 8),
      deriv (raisedReturnPlanarCurve J2 h inner) t ≠ 0 := by
    intro t ht
    by_cases htl : t ≤ h
    · have hRder : deriv (raisedReturnRadius h) t = -1 := by
        rw [hleftD (raisedReturnRadius h) (raisedReturnRadius_contDiff h) h
          (1 + 3 * h) (-1)
          (fun s hs => by
            rw [raisedReturn_left_formula h hh hsmall s hs]
            ring) t htl]
      have hAder : deriv (raisedReturnAngle h) t = 0 := by
        rw [hleftD (raisedReturnAngle h) (raisedReturnAngle_contDiff h) h
          (3 * Real.pi / 4) 0
          (fun s hs => by
            have hq := raisedReturn_q_zero_left h hh hsmall s hs
            unfold raisedReturnAngle
            rw [hq]
            ring) t htl]
      have hp : deriv (fun s : ℝ =>
          (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s),
            raisedReturnRadius h s * Real.sin (raisedReturnAngle h s))) t ≠ 0 := by
        intro hz
        have hz' := hz
        rw [(hpairHasDeriv t).deriv] at hz'
        have hx := congrArg Prod.fst hz'
        have hy := congrArg Prod.snd hz'
        have hx' : deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t) = 0 := by
          simpa [hAder] using hx
        have hy' : deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t) = 0 := by
          simpa [hAder] using hy
        have hzR : deriv (raisedReturnRadius h) t = 0 := by
          calc
            deriv (raisedReturnRadius h) t = deriv (raisedReturnRadius h) t *
                (Real.sin (raisedReturnAngle h t) ^ 2 +
                  Real.cos (raisedReturnAngle h t) ^ 2) := by
              rw [Real.sin_sq_add_cos_sq]
              ring
            _ = Real.cos (raisedReturnAngle h t) *
                (deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t)) +
                Real.sin (raisedReturnAngle h t) *
                  (deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t)) := by ring
            _ = 0 := by rw [hx', hy']; ring
        have hz' : (-1 : ℝ) = 0 := hRder ▸ hzR
        norm_num at hz'
      exact hplanarRegular_of_pair t hp
    by_cases htr : 1 - h ≤ t
    · have hRder : deriv (raisedReturnRadius h) t = 1 := by
        rw [hrightD (raisedReturnRadius h) (raisedReturnRadius_contDiff h) (1 - h)
          (3 * h) 1
          (fun s hs => by
            rw [raisedReturn_right_formula h hh hsmall s hs]
            ring) t htr]
      have hAder : deriv (raisedReturnAngle h) t = 0 := by
        rw [hrightD (raisedReturnAngle h) (raisedReturnAngle_contDiff h) (1 - h)
          (9 * Real.pi / 4) 0
          (fun s hs => by
            have hq := raisedReturn_q_one_right h hh hsmall s hs
            unfold raisedReturnAngle
            rw [hq]
            ring) t htr]
      have hp : deriv (fun s : ℝ =>
          (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s),
            raisedReturnRadius h s * Real.sin (raisedReturnAngle h s))) t ≠ 0 := by
        intro hz
        have hz' := hz
        rw [(hpairHasDeriv t).deriv] at hz'
        have hx := congrArg Prod.fst hz'
        have hy := congrArg Prod.snd hz'
        have hx' : deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t) = 0 := by
          simpa [hAder] using hx
        have hy' : deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t) = 0 := by
          simpa [hAder] using hy
        have hzR : deriv (raisedReturnRadius h) t = 0 := by
          calc
            deriv (raisedReturnRadius h) t = deriv (raisedReturnRadius h) t *
                (Real.sin (raisedReturnAngle h t) ^ 2 +
                  Real.cos (raisedReturnAngle h t) ^ 2) := by
              rw [Real.sin_sq_add_cos_sq]
              ring
            _ = Real.cos (raisedReturnAngle h t) *
                (deriv (raisedReturnRadius h) t * Real.cos (raisedReturnAngle h t)) +
                Real.sin (raisedReturnAngle h t) *
                  (deriv (raisedReturnRadius h) t * Real.sin (raisedReturnAngle h t)) := by ring
            _ = 0 := by rw [hx', hy']; ring
        have hz' : (1 : ℝ) = 0 := hRder ▸ hzR
        norm_num at hz'
      exact hplanarRegular_of_pair t hp
    have hmid : h < t ∧ t < 1 - h := by
      exact ⟨lt_of_not_ge htl, lt_of_not_ge htr⟩
    have hd : 0 < 1 - 2 * h := by linarith
    have harg : (t - h) / (1 - 2 * h) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by linarith [hmid.1]) hd
      · exact (div_lt_one hd).mpr (by linarith [hmid.2])
    have hAd : HasDerivAt (raisedReturnAngle h)
        ((3 * Real.pi / 2) *
          (deriv Real.smoothTransition ((t - h) / (1 - 2 * h)) *
            (1 / (1 - 2 * h)))) t := by
      have hqder : HasDerivAt (raisedReturnQ h)
          (deriv Real.smoothTransition ((t - h) / (1 - 2 * h)) *
            (1 / (1 - 2 * h))) t := by
        unfold raisedReturnQ
        simpa only [Function.comp_def, id_eq, one_div] using
          (Real.smoothTransition.contDiff.differentiable_one.differentiableAt).hasDerivAt.comp t
            (((hasDerivAt_id t).sub_const h).div_const (1 - 2 * h))
      change HasDerivAt
        (fun s : ℝ => 3 * Real.pi / 4 + (3 * Real.pi / 2) * raisedReturnQ h s) _ t
      exact (hqder.const_mul (3 * Real.pi / 2)).const_add (3 * Real.pi / 4)
    have hApos : 0 < deriv (raisedReturnAngle h) t := by
      rw [hAd.deriv]
      have hv := saddle_smoothTransition_regular.1 _ harg
      have hden : 0 < (1 / (1 - 2 * h) : ℝ) := one_div_pos.mpr hd
      exact mul_pos (by positivity) (mul_pos hv hden)
    exact hplanarRegular_of_pair t (Real.polar_deriv_ne_zero_of_pos
      (raisedReturnRadius h) (raisedReturnAngle h) t
      ((raisedReturnRadius_contDiff h).differentiable (by simp) t)
      ((raisedReturnAngle_contDiff h).differentiable (by simp) t)
      (lt_of_lt_of_le (by linarith) (raisedReturnRadius_lower h hh t)) hApos)
  have hphysicalRegular : ∀ t ∈ Ioo (-h / 8) (1 + h / 8),
      deriv (raisedReturnPhysicalCurve kappa J2 h inner) t ≠ 0 := by
    intro t ht
    obtain ⟨L, hL⟩ := exists_smoothChart_derivative kappa hkappa hkappaInv (hsource t ht)
    have hd : HasDerivAt (kappa ∘ raisedReturnPlanarCurve J2 h inner)
        (L (deriv (raisedReturnPlanarCurve J2 h inner) t)) t :=
      hL.comp_hasDerivAt t (hcurveSmooth.differentiable (by simp) t).hasDerivAt
    intro he
    change deriv (kappa ∘ raisedReturnPlanarCurve J2 h inner) t = 0 at he
    rw [hd.deriv] at he
    have he' : L (deriv (raisedReturnPlanarCurve J2 h inner) t) = L 0 := by
      simpa only [map_zero] using he
    exact hcurveRegular t ht (L.injective he')
  have hdisjoint : Disjoint
      (raisedReturnPhysicalCurve kappa J2 h inner '' Icc (0 : ℝ) 1)
      (beta '' Icc (0 : ℝ) 1) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨t, ht, hty⟩ ⟨u, hu, huy⟩
    rcases hbeta hu with ⟨x, hx, hxbeta⟩
    have htU : t ∈ Ioo (-h / 8) (1 + h / 8) := by
      constructor <;> nlinarith [ht.1, ht.2, hh]
    have hxsource : x ∈ kappa.source := by
      apply hkappaSource
      rw [mem_closedBall_zero_iff]
      exact le_of_lt (by nlinarith [hx.2.1, hsmall])
    have heq : kappa (raisedReturnPlanarCurve J2 h inner t) = kappa x := by
      calc
        kappa (raisedReturnPlanarCurve J2 h inner t) =
            raisedReturnPhysicalCurve kappa J2 h inner t := rfl
        _ = y := hty
        _ = beta u := huy.symm
        _ = kappa x := hxbeta.symm
    have hgtx := kappa.injOn (hsource t htU) hxsource heq
    have hsector : |(J2 (raisedReturnPlanarCurve J2 h inner t)).1| ≤
        raisedReturnSign inner * (J2 (raisedReturnPlanarCurve J2 h inner t)).2 := by
      rw [hgtx]
      exact hx.2.2
    have hq := raisedReturn_opposite_sector_q J2 h hh hsmall inner t ht hsector
    have hR10 := raisedReturn_radius_lower_of_opposite_sector h hh t hq
    have hnormeq : raisedReturnRadius h t = ‖x‖ := by
      calc
        raisedReturnRadius h t = ‖raisedReturnPlanarCurve J2 h inner t‖ :=
          (hcurveNorm t).symm
        _ = ‖x‖ := congrArg norm hgtx
    linarith [hR10, hx.2.1, hh]
  have hangleBounds (t : ℝ) :
      raisedReturnAngle h t ∈ Icc (3 * Real.pi / 4) (9 * Real.pi / 4) := by
    have hq := raisedReturnQ_bounds h t
    unfold raisedReturnAngle
    constructor <;> nlinarith [Real.pi_pos, hq.1, hq.2]
  have hcurveInj : Set.InjOn (raisedReturnPlanarCurve J2 h inner)
      (Ioo (-h / 8) (1 + h / 8)) := by
    have hd : 0 < 1 - 2 * h := by linarith
    have hq_zero_imp (x : ℝ) (hx : raisedReturnQ h x = 0) : x ≤ h := by
      unfold raisedReturnQ at hx
      have hz := (Real.smoothTransition.zero_iff_nonpos).mp hx
      rcases (div_nonpos_iff.mp hz) with hp | hn
      · linarith
      · linarith
    have hq_one_imp (x : ℝ) (hx : raisedReturnQ h x = 1) : 1 - h ≤ x := by
      unfold raisedReturnQ at hx
      have hz := (Real.smoothTransition.eq_one_iff_one_le).mp hx
      have hz' := (le_div_iff₀ hd).mp hz
      linarith
    intro s hs t ht he
    have hsR : 0 < raisedReturnRadius h s :=
      lt_of_lt_of_le (by linarith) (raisedReturnRadius_lower h hh s)
    have htR : 0 < raisedReturnRadius h t :=
      lt_of_lt_of_le (by linarith) (raisedReturnRadius_lower h hh t)
    have heJ : J2 (raisedReturnPlanarCurve J2 h inner s) =
        J2 (raisedReturnPlanarCurve J2 h inner t) := congrArg J2 he
    dsimp [raisedReturnPlanarCurve] at heJ
    simp only [J2.apply_symm_apply] at heJ
    have hsign := raisedReturnSign_sq (raisedReturnOther inner)
    have hePair :
        (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s),
          raisedReturnRadius h s * Real.sin (raisedReturnAngle h s)) =
        (raisedReturnRadius h t * Real.cos (raisedReturnAngle h t),
          raisedReturnRadius h t * Real.sin (raisedReturnAngle h t)) := by
      have he' := congrArg (fun p : ℝ × ℝ =>
          (raisedReturnSign (raisedReturnOther inner) * p.1,
            raisedReturnSign (raisedReturnOther inner) * p.2)) heJ
      apply Prod.ext
      · have hx := congrArg Prod.fst he'
        change raisedReturnSign (raisedReturnOther inner) *
            (raisedReturnSign (raisedReturnOther inner) *
              raisedReturnRadius h s * Real.cos (raisedReturnAngle h s)) =
          raisedReturnSign (raisedReturnOther inner) *
            (raisedReturnSign (raisedReturnOther inner) *
              raisedReturnRadius h t * Real.cos (raisedReturnAngle h t)) at hx
        calc
          _ = raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s))) := by
            rw [show raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s))) =
                raisedReturnSign (raisedReturnOther inner) ^ 2 *
                  (raisedReturnRadius h s * Real.cos (raisedReturnAngle h s)) by ring,
              hsign, one_mul]
          _ = raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h t * Real.cos (raisedReturnAngle h t))) := by
            simpa only [mul_assoc] using hx
          _ = _ := by
            rw [show raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h t * Real.cos (raisedReturnAngle h t))) =
                raisedReturnSign (raisedReturnOther inner) ^ 2 *
                  (raisedReturnRadius h t * Real.cos (raisedReturnAngle h t)) by ring,
              hsign, one_mul]
      · have hy := congrArg Prod.snd he'
        change raisedReturnSign (raisedReturnOther inner) *
            (raisedReturnSign (raisedReturnOther inner) *
              raisedReturnRadius h s * Real.sin (raisedReturnAngle h s)) =
          raisedReturnSign (raisedReturnOther inner) *
            (raisedReturnSign (raisedReturnOther inner) *
              raisedReturnRadius h t * Real.sin (raisedReturnAngle h t)) at hy
        calc
          _ = raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h s * Real.sin (raisedReturnAngle h s))) := by
            rw [show raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h s * Real.sin (raisedReturnAngle h s))) =
                raisedReturnSign (raisedReturnOther inner) ^ 2 *
                  (raisedReturnRadius h s * Real.sin (raisedReturnAngle h s)) by ring,
              hsign, one_mul]
          _ = raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h t * Real.sin (raisedReturnAngle h t))) := by
            simpa only [mul_assoc] using hy
          _ = _ := by
            rw [show raisedReturnSign (raisedReturnOther inner) *
              (raisedReturnSign (raisedReturnOther inner) *
                (raisedReturnRadius h t * Real.sin (raisedReturnAngle h t))) =
                raisedReturnSign (raisedReturnOther inner) ^ 2 *
                  (raisedReturnRadius h t * Real.sin (raisedReturnAngle h t)) by ring,
              hsign, one_mul]
    have hpolar := Real.polar_parameters_eq_of_mem_Icc
      hsR htR (hangleBounds s) (hangleBounds t) (by nlinarith [Real.pi_pos]) hePair
    have hReq : raisedReturnRadius h s = raisedReturnRadius h t := hpolar.1
    have hAeq : raisedReturnAngle h s = raisedReturnAngle h t := hpolar.2
    have hQeq : raisedReturnQ h s = raisedReturnQ h t := by
      unfold raisedReturnAngle at hAeq
      nlinarith [Real.pi_pos, hAeq]
    by_cases hsL : s ≤ h
    · have hsQ : raisedReturnQ h s = 0 := raisedReturn_q_zero_left h hh hsmall s hsL
      have htQ : raisedReturnQ h t = 0 := hQeq ▸ hsQ
      have htL := hq_zero_imp t htQ
      have hsr := raisedReturn_left_formula h hh hsmall s hsL
      have htr := raisedReturn_left_formula h hh hsmall t htL
      rw [hsr, htr] at hReq
      linarith
    by_cases hsRgt : 1 - h ≤ s
    · have hsQ : raisedReturnQ h s = 1 := raisedReturn_q_one_right h hh hsmall s hsRgt
      have htQ : raisedReturnQ h t = 1 := hQeq ▸ hsQ
      have htRgt := hq_one_imp t htQ
      have hsr := raisedReturn_right_formula h hh hsmall s hsRgt
      have htr := raisedReturn_right_formula h hh hsmall t htRgt
      rw [hsr, htr] at hReq
      linarith
    have hsMid : h < s ∧ s < 1 - h := ⟨lt_of_not_ge hsL, lt_of_not_ge hsRgt⟩
    have hqSpos : 0 < raisedReturnQ h s := by
      unfold raisedReturnQ
      apply Real.smoothTransition.pos_of_pos
      exact (div_pos_iff.mpr (Or.inl ⟨by linarith [hsMid.1], hd⟩))
    have hqSlt : raisedReturnQ h s < 1 := by
      unfold raisedReturnQ
      apply Real.smoothTransition.lt_one_of_lt_one
      apply (div_lt_iff₀ hd).2
      linarith [hsMid.2]
    have htMid : h < t ∧ t < 1 - h := by
      constructor
      · by_contra hnot
        have htL : t ≤ h := le_of_not_gt hnot
        have htQ := raisedReturn_q_zero_left h hh hsmall t htL
        linarith [hqSpos, hQeq, htQ]
      · by_contra hnot
        have htRgt : 1 - h ≤ t := le_of_not_gt hnot
        have htQ := raisedReturn_q_one_right h hh hsmall t htRgt
        linarith [hqSlt, hQeq, htQ]
    have hsArg : (s - h) / (1 - 2 * h) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact (div_nonneg_iff.mpr (Or.inl ⟨by linarith [hsMid.1], hd.le⟩))
      · exact (div_le_one hd).mpr (by linarith [hsMid.2])
    have htArg : (t - h) / (1 - 2 * h) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact (div_nonneg_iff.mpr (Or.inl ⟨by linarith [htMid.1], hd.le⟩))
      · exact (div_le_one hd).mpr (by linarith [htMid.2])
    have hArgEq : (s - h) / (1 - 2 * h) = (t - h) / (1 - 2 * h) := by
      apply (saddle_smoothTransition_regular.2.injOn hsArg htArg)
      exact hQeq
    have hArgEq' := (div_left_inj' hd.ne').mp hArgEq
    linarith
  have hphysicalInj : Set.InjOn (raisedReturnPhysicalCurve kappa J2 h inner)
      (Ioo (-h / 8) (1 + h / 8)) := by
    intro s hs t ht he
    change kappa (raisedReturnPlanarCurve J2 h inner s) =
      kappa (raisedReturnPlanarCurve J2 h inner t) at he
    exact hcurveInj hs ht (kappa.injOn (hsource s hs) (hsource t ht) he)
  have hmid : raisedReturnPlanarCurve J2 h inner (1 / 2) =
      J2.symm (0, raisedReturnSign inner * (1 + 10 * h)) :=
    raisedReturn_mid_formula h hh hsmall J2 inner
  have hleft : ∀ t ∈ Ioo (-h / 8) (1 + h / 8), t ≤ h →
      raisedReturnPhysicalCurve kappa J2 h inner t = kappa (J2.symm
        (raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h - t) *
            Real.cos (3 * Real.pi / 4),
          raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h - t) *
            Real.sin (3 * Real.pi / 4))) := by
    intro t _ht htl
    have hq := raisedReturn_q_zero_left h hh hsmall t htl
    have hr := raisedReturn_left_formula h hh hsmall t htl
    have ha : raisedReturnAngle h t = 3 * Real.pi / 4 := by
      unfold raisedReturnAngle
      rw [hq]
      ring
    simp [raisedReturnPhysicalCurve, raisedReturnPlanarCurve, hr, ha]
  have hright : ∀ t ∈ Ioo (-h / 8) (1 + h / 8), 1 - h ≤ t →
      raisedReturnPhysicalCurve kappa J2 h inner t = kappa (J2.symm
        (raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h + t - 1) *
            Real.cos (9 * Real.pi / 4),
          raisedReturnSign (raisedReturnOther inner) * (1 + 3 * h + t - 1) *
            Real.sin (9 * Real.pi / 4))) := by
    intro t _ht htr
    have hq := raisedReturn_q_one_right h hh hsmall t htr
    have hr := raisedReturn_right_formula h hh hsmall t htr
    have ha : raisedReturnAngle h t = 9 * Real.pi / 4 := by
      unfold raisedReturnAngle
      rw [hq]
      ring
    simp [raisedReturnPhysicalCurve, raisedReturnPlanarCurve, hr, ha]
  refine ⟨raisedReturnPlanarCurve J2 h inner,
    raisedReturnPhysicalCurve kappa J2 h inner, rfl, rfl, hcurveSmooth,
    hphysicalSmooth, hcurveInj, hphysicalInj, ?_, ?_, ?_, hradius, hmid,
    hleft, hright, hbeta, ?_⟩
  · intro t ht
    exact ⟨hcurveRegular t ht, hphysicalRegular t ht⟩
  · intro t
    rfl
  · intro t ht
    exact ⟨hsource t ht, (hbuffer t ht).1, (hbuffer t ht).2⟩
  · simpa using hdisjoint

end PoincareConjecture.M25.Topology3D
