import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CenteredCutoffArcs
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLoss
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcTurning
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.IntegratedLocalizedTurning

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff intervalIntegral Topology

universe u

namespace PoincareConjecture

open M62

variable {n : Nat} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : Real}

theorem m63SmallSubarcs_transport_of_curvature_bound
    (F : RicciFlow n M (Icc a b)) (c : Real → Real → M)
    (hc : M62ShrinkingCurve F c) {K E : Real}
    (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {P1 P2 : Real} (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2)
    (psi : Real → Real) (hpsi : ContDiff Real 2 psi)
    (hRange : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
    (hPlateau : ∀ z, |z| ≤ 3 / 8 → psi z = 1)
    (hSupport : tsupport psi ⊆ Ioo (-(9 / 20 : Real)) (9 / 20 : Real))
    (hFirst : ∀ z, |deriv psi z| ≤ P1)
    (hSecond : ∀ z, |deriv (deriv psi) z| ≤ P2)
    {s T r delta : Real} (hs : a ≤ s) (hsT : s < T) (hT : T ≤ b)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hTime : T - s ≤ delta * r ^ 2)
    (hLength : r ≤ m62Length F c s)
    (hGlobal : ∀ t ∈ Icc s T,
      m62Length F c t ≤ E ∧ m62TotalCurvature F c t ≤ E)
    (hSmall : M63SmallSubarcs F c s r delta)
    (hCurv : ∀ t ∈ Ioo s T, ∀ x, m62CurvatureSquared F c t x ≤ 2 / (t - s))
    (hLoss : K * Real.exp K * delta +
      2 * Real.sqrt 2 * E * Real.sqrt delta ≤ 1 / 20)
    (hExp : Real.exp (K * delta) ≤ 3 / 2) :
    let C1 := m62C1 K K K
    let D := (P2 + P1 * K * E + (C1 + K)) * E + C1 * E +
      2 * P1 * Real.sqrt 2 * E ^ 2
    ∀ t ∈ Icc s T,
      M63SmallSubarcs F c t (r / 2) (2 * (delta + D * Real.sqrt delta)) := by
  let C1 := m62C1 K K K
  let A := (P2 + P1 * K * E + (C1 + K)) * E + C1 * E
  let B := 2 * P1 * Real.sqrt 2 * E ^ 2
  change ∀ t ∈ Icc s T, M63SmallSubarcs F c t (r / 2)
    (2 * (delta + (A + B) * Real.sqrt delta))
  have hC1 : 0 ≤ C1 := by dsimp only [C1, m62C1, m62C0]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hr2 : r ^ 2 ≤ 1 := by nlinarith only [hr.le, hr1]
  have hclosed (t : Real) (ht : t ∈ Icc s T) : t ∈ Icc a b :=
    ⟨hs.trans ht.1, ht.2.trans hT⟩
  have hsclosed : s ∈ Icc a b := hclosed s ⟨le_rfl, hsT.le⟩
  have hage (t : Real) (ht : t ∈ Icc s T) : t - s ≤ delta * r ^ 2 :=
    (sub_le_sub_right ht.2 s).trans hTime
  have hageDelta (t : Real) (ht : t ∈ Icc s T) : t - s ≤ delta :=
    (hage t ht).trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hr2 hd.le)
  have hsqrt (t : Real) (ht : t ∈ Icc s T) :
      Real.sqrt (t - s) ≤ Real.sqrt delta * r := by
    have h := Real.sqrt_le_sqrt (hage t ht)
    simpa only [Real.sqrt_mul hd.le, Real.sqrt_sq hr.le] using h
  have hdroot : delta ≤ Real.sqrt delta := by
    nlinarith only [Real.sq_sqrt hd.le, Real.sqrt_nonneg delta, hd.le, hd1,
      mul_nonneg hd.le (sub_nonneg.mpr hd1)]
  have hv (t : Real) (ht : t ∈ Icc a b) : Continuous (curveSpeed F c t) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hk (t : Real) (ht : t ∈ Icc a b) : Continuous (m62Curvature F c t) :=
    (curvature_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hloss {alpha beta : Real} (hab : alpha ≤ beta)
      (hperiod : beta ≤ alpha + curvePeriod)
      (hinit : m63ArcLength F c s alpha beta ≤ r)
      (t : Real) (ht : t ∈ Icc s T) :
      m63ArcLength F c s alpha beta ≤ m63ArcLength F c t alpha beta + r / 20 := by
    have hL (tau : Real) (htau : tau ∈ Ioo s T) :
        m63ArcLength F c tau alpha beta ≤ Real.exp K * r := by
      have htau' := Ioo_subset_Icc_self htau
      have he : Real.exp (K * (tau - s)) ≤ Real.exp K :=
        Real.exp_le_exp.mpr (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            ((hageDelta tau htau').trans hd1) hK)
      calc
        _ ≤ m63ArcLength F c s alpha beta * Real.exp (K * (tau - s)) :=
          m63ArcLength_le_mul_exp F c hc hBounds hab hsclosed (hclosed tau htau') htau.1.le
        _ ≤ r * Real.exp (K * (tau - s)) :=
          mul_le_mul_of_nonneg_right hinit (Real.exp_pos _).le
        _ ≤ r * Real.exp K := mul_le_mul_of_nonneg_left he hr.le
        _ = Real.exp K * r := mul_comm _ _
    have hturn (tau : Real) (htau : tau ∈ Ioo s T) :
        m63ArcTotalCurvature F c tau alpha beta ≤ E :=
      (m63ArcTotalCurvature_le_total F c hc hab hperiod
        (hclosed tau (Ioo_subset_Icc_self htau))).trans
        (hGlobal tau (Ioo_subset_Icc_self htau)).2
    have hraw := m63ArcLength_backward_loss F c hc hBounds hK hab hs hT hsT hE hL hturn
      (fun tau htau x _ => hCurv tau htau x) ht
    have hlin : K * (Real.exp K * r) * (t - s) ≤ K * (Real.exp K * r) * delta :=
      mul_le_mul_of_nonneg_left (hageDelta t ht) (by positivity)
    have hroot := mul_le_mul_of_nonneg_left (hsqrt t ht)
      (show 0 ≤ 2 * Real.sqrt 2 * E by positivity)
    have htotal : K * (Real.exp K * r) * (t - s) +
        2 * Real.sqrt 2 * E * Real.sqrt (t - s) ≤ r / 20 := by
      calc
        _ ≤ K * (Real.exp K * r) * delta +
            2 * Real.sqrt 2 * E * (Real.sqrt delta * r) := add_le_add hlin hroot
        _ = (K * Real.exp K * delta + 2 * Real.sqrt 2 * E * Real.sqrt delta) * r := by ring
        _ ≤ (1 / 20 : Real) * r := mul_le_mul_of_nonneg_right hLoss hr.le
        _ = r / 20 := by ring
    linarith only [hraw, htotal]
  have hinner {alpha beta : Real} (hab : alpha ≤ beta)
      (hperiod : beta ≤ alpha + curvePeriod)
      (hinit : m63ArcLength F c s alpha beta ≤ r / 2)
      (t : Real) (ht : t ∈ Icc s T) :
      m63ArcTotalCurvature F c t alpha beta ≤ delta + (A + B) * Real.sqrt delta := by
    obtain ⟨lo, x0, hi, hlo, hax, hxb, hhi, hperiod', hleft, hright,
      hwhole, hinnerLeft, hinnerRight⟩ :=
      m63ArcLength_exists_centered_enlargement F c hc hsclosed hr hLength hab hperiod hinit
    have houter : lo ≤ hi := hlo.trans (hab.trans hhi)
    have hleftOrder : lo ≤ x0 := hlo.trans hax
    have hrightOrder : x0 ≤ hi := hxb.trans hhi
    have hguardLeft (tau : Real) (htau : tau ∈ Ioo s T) :
        (9 / 20 : Real) * r ≤ m63ArcLength F c tau lo x0 := by
      have h := hloss hleftOrder (hxb.trans (hhi.trans hperiod'))
        (by rw [hleft]; linarith only [hr]) tau (Ioo_subset_Icc_self htau)
      rw [hleft] at h
      linarith only [h]
    have hguardRight (tau : Real) (htau : tau ∈ Ioo s T) :
        (9 / 20 : Real) * r ≤ m63ArcLength F c tau x0 hi := by
      have hp : hi ≤ x0 + curvePeriod := hperiod'.trans (add_le_add hleftOrder le_rfl)
      have h := hloss hrightOrder hp (by rw [hright]; linarith only [hr])
        tau (Ioo_subset_Icc_self htau)
      rw [hright] at h
      linarith only [h]
    let f : Real → Real → Real := fun tau x =>
      psi (m63ArcLength F c tau x0 x / r) * m62Curvature F c tau x * curveSpeed F c tau x
    let I : Real → Real := fun tau => ∫ x in lo..hi, f tau x
    let D0 := (P2 / r ^ 2 + (P1 / r) * K * E + (C1 + K)) * E + C1 * E
    let D1 := (P1 / r) * Real.sqrt 2 * E ^ 2
    have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
    have hD1 : 0 ≤ D1 := by dsimp only [D1]; positivity
    have hfc (tau : Real) (htau : tau ∈ Icc a b) : Continuous (f tau) := by
      have hsigma : Continuous (fun x => m63ArcLength F c tau x0 x) :=
        (m63ArcLength_joint_continuousOn F c hc x0).comp_continuous
          (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, htau⟩)
      exact ((hpsi.continuous.comp (hsigma.div_const r)).mul (hk tau htau)).mul (hv tau htau)
    have hf0 (tau x : Real) : 0 ≤ f tau x :=
      mul_nonneg (mul_nonneg (hRange _).1 (curvature_nonneg F c tau x)) (speed_nonneg F c tau x)
    have hstart : I s ≤ delta := by
      calc
        _ ≤ m63ArcTotalCurvature F c s lo hi := by
          apply intervalIntegral.integral_mono_on houter ((hfc s hsclosed).intervalIntegrable _ _)
            (((hk s hsclosed).mul (hv s hsclosed)).intervalIntegrable _ _)
          intro x _
          exact mul_le_mul_of_nonneg_right
            (mul_le_of_le_one_left (curvature_nonneg F c s x) (hRange _).2)
            (speed_nonneg F c s x)
        _ ≤ delta := hSmall lo hi houter hperiod' hwhole.le
    have hplateau : ∀ x ∈ Icc alpha beta, psi (m63ArcLength F c t x0 x / r) = 1 :=
      m63ArcCutoff_eq_one_of_half_lengths F c hc hBounds hsclosed (hclosed t ht) ht.1 hr
        hax hxb (by rw [hinnerLeft]; linarith only [hinit])
        (by rw [hinnerRight]; linarith only [hinit])
        ((Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hageDelta t ht) hK)).trans hExp)
        psi hPlateau
    have hfinish : m63ArcTotalCurvature F c t alpha beta ≤ I t := by
      calc
        _ = ∫ x in alpha..beta, f t x := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Icc alpha beta := (uIcc_of_le hab ▸ hx)
          dsimp only [f]
          rw [hplateau x hx', one_mul]
        _ ≤ I t := intervalIntegral.integral_mono_interval hlo hab hhi
          (Eventually.of_forall (hf0 t)) ((hfc t (hclosed t ht)).intervalIntegrable _ _)
    have hraw : I t ≤ I s + D0 * (t - s) + 2 * D1 * Real.sqrt (t - s) :=
      m63ArcCutoff_turning_increase_le F c hc hK hK hK hBounds houter
        ⟨hleftOrder, hrightOrder⟩ hr hP1 hP2 psi hpsi hRange hSupport hFirst hSecond
        hs hT hsT hE hE
        (fun tau htau => (m63ArcLength_le_length F c hc houter hperiod'
          (hclosed tau (Ioo_subset_Icc_self htau))).trans
          (hGlobal tau (Ioo_subset_Icc_self htau)).1)
        (fun tau htau => (m63ArcTotalCurvature_le_total F c hc houter hperiod'
          (hclosed tau (Ioo_subset_Icc_self htau))).trans
          (hGlobal tau (Ioo_subset_Icc_self htau)).2)
        (fun tau htau x _ => hCurv tau htau x) hguardLeft hguardRight ht
    have hscaled : D0 * r ^ 2 ≤ A := by
      have heq : D0 * r ^ 2 =
          (P2 + P1 * K * E * r + (C1 + K) * r ^ 2) * E + C1 * E * r ^ 2 := by
        dsimp only [D0]
        field_simp [hr.ne']
      rw [heq]
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (add_le_add (add_le_add le_rfl (by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1
              (show 0 ≤ P1 * K * E by positivity)))
            (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr2 (add_nonneg hC1 hK))) hE)
        (by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hr2 (mul_nonneg hC1 hE))
    have hlinear : D0 * (t - s) ≤ A * Real.sqrt delta := by
      calc
        _ ≤ D0 * (delta * r ^ 2) := mul_le_mul_of_nonneg_left (hage t ht) hD0
        _ = (D0 * r ^ 2) * delta := by ring
        _ ≤ A * delta := mul_le_mul_of_nonneg_right hscaled hd.le
        _ ≤ A * Real.sqrt delta := mul_le_mul_of_nonneg_left hdroot hA
    have hroot : 2 * D1 * Real.sqrt (t - s) ≤ B * Real.sqrt delta := by
      calc
        _ ≤ 2 * D1 * (Real.sqrt delta * r) :=
          mul_le_mul_of_nonneg_left (hsqrt t ht) (mul_nonneg (by norm_num) hD1)
        _ = B * Real.sqrt delta := by
          dsimp only [D1, B]
          field_simp [hr.ne']
    linarith only [hfinish, hraw, hstart, hlinear, hroot]
  obtain ⟨_, sigma, hformula, _, _, _, hpos, _, _, _⟩ :=
    M63.exists_c2_unit_speed_parameter F (fun x => c x s) s
      (hc.periodic s hsclosed) (hc.spatial_regular s hsclosed) (hc.immersed s hsclosed)
  have hmono : StrictMono (sigma : Real → Real) := strictMono_of_deriv_pos hpos
  have hprimitive (x y : Real) : m63ArcLength F c s x y = sigma y - sigma x := by
    rw [hformula y, hformula x]
    exact (intervalIntegral.integral_interval_sub_left
      ((hv s hsclosed).intervalIntegrable 0 y) ((hv s hsclosed).intervalIntegrable 0 x)).symm
  intro t ht alpha beta hab hperiod hcurrent
  have hinit : m63ArcLength F c s alpha beta ≤ r := by
    by_contra! hlarge
    let z : Real := sigma.symm (sigma alpha + r)
    have hz : sigma z = sigma alpha + r := sigma.apply_symm_apply _
    have haz : alpha ≤ z := hmono.le_iff_le.mp (by rw [hz]; linarith only [hr])
    have hzb : z ≤ beta := hmono.le_iff_le.mp (by
      rw [hz]
      rw [hprimitive] at hlarge
      linarith only [hlarge])
    have hlen : m63ArcLength F c s alpha z = r := by rw [hprimitive, hz]; ring
    have hl := hloss haz (hzb.trans hperiod) hlen.le t ht
    have hm : m63ArcLength F c t alpha z ≤ m63ArcLength F c t alpha beta :=
      intervalIntegral.integral_mono_interval le_rfl haz hzb
        (Eventually.of_forall (speed_nonneg F c t)) ((hv t (hclosed t ht)).intervalIntegrable _ _)
    rw [hlen] at hl
    linarith only [hl, hm, hcurrent, hr]
  let z : Real := sigma.symm ((sigma alpha + sigma beta) / 2)
  have hz : sigma z = (sigma alpha + sigma beta) / 2 := sigma.apply_symm_apply _
  have horder := hmono.monotone hab
  have haz : alpha ≤ z := hmono.le_iff_le.mp (by rw [hz]; linarith only [horder])
  have hzb : z ≤ beta := hmono.le_iff_le.mp (by rw [hz]; linarith only [horder])
  have hleft : m63ArcLength F c s alpha z ≤ r / 2 := by
    rw [hprimitive, hz]
    rw [hprimitive] at hinit
    linarith only [hinit]
  have hright : m63ArcLength F c s z beta ≤ r / 2 := by
    rw [hprimitive, hz]
    rw [hprimitive] at hinit
    linarith only [hinit]
  have hturnLeft := hinner haz (hzb.trans hperiod) hleft t ht
  have hturnRight := hinner hzb (hperiod.trans (add_le_add haz le_rfl)) hright t ht
  have hcont := (hk t (hclosed t ht)).mul (hv t (hclosed t ht))
  have hadd : m63ArcTotalCurvature F c t alpha z + m63ArcTotalCurvature F c t z beta =
      m63ArcTotalCurvature F c t alpha beta :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable alpha z) (hcont.intervalIntegrable z beta)
  linarith only [hturnLeft, hturnRight, hadd]

end PoincareConjecture
