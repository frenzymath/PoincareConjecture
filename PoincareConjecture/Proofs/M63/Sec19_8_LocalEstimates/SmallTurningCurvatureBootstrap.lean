import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.SmallSubarcTurningTransport
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureOscillationUnderBootstrap
import Mathlib.Algebra.Field.Periodic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture

open M62

variable {n : Nat} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : Real}

theorem m63SmallSubarcs_curvature_bound
    (F : RicciFlow n M (Icc a b)) (c : Real → Real → M)
    (hc : M62ShrinkingCurve F c) {K E : Real}
    (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hRiemann : ∀ t ∈ Icc a b, ∀ p : M,
      ∀ v : Fin 5 → TangentSpace (𝓡 n) p,
      (∀ i, (F.metric t).tangentNorm p (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          (F.connection t).riemannEvaluation p v| ≤ K)
    (hSecond : ∀ t ∈ Icc a b, ∀ p : M,
      ∀ v : Fin 4 → TangentSpace (𝓡 n) p,
      (∀ i, (F.metric t).tangentNorm p (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).ricciEvaluation) p v| ≤ K)
    {P1 P2 : Real} (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2)
    (psi : Real → Real) (hpsi : ContDiff Real 2 psi)
    (hRange : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
    (hPlateau : ∀ z, |z| ≤ 3 / 8 → psi z = 1)
    (hSupport : tsupport psi ⊆ Ioo (-(9 / 20 : Real)) (9 / 20 : Real))
    (hFirst : ∀ z, |deriv psi z| ≤ P1)
    (hSecondPsi : ∀ z, |deriv (deriv psi) z| ≤ P2)
    {s T r delta : Real} (hs : a ≤ s) (hsT : s < T) (hT : T ≤ b)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hTime : T - s ≤ delta * r ^ 2)
    (hLength : r ≤ m62Length F c s)
    (hGlobal : ∀ t ∈ Icc s T,
      m62Length F c t ≤ E ∧ m62TotalCurvature F c t ≤ E)
    (hSmall : M63SmallSubarcs F c s r delta)
    (hLoss : K * Real.exp K * delta +
      2 * Real.sqrt 2 * E * Real.sqrt delta ≤ 1 / 20)
    (hExp : Real.exp (K * delta) ≤ 3 / 2) :
    let C1 := m62C1 K K K
    let D := (P2 + P1 * K * E + (C1 + K)) * E + C1 * E +
      2 * P1 * Real.sqrt 2 * E ^ 2
    let B := (272 + 17 * m62C0 K K K) * (114 + 10 * K) +
      2048 + 992 * K + 160000 * K ^ 2
    let h := min (1 / 4 : Real) (1 / (8 * Real.sqrt B + 1))
    2 * (delta + D * Real.sqrt delta) < h →
      ∀ t ∈ Ioc s T, ∀ x, m62CurvatureSquared F c t x ≤ 2 / (t - s) := by
  classical
  let C1 := m62C1 K K K
  let D := (P2 + P1 * K * E + (C1 + K)) * E + C1 * E +
    2 * P1 * Real.sqrt 2 * E ^ 2
  let B := (272 + 17 * m62C0 K K K) * (114 + 10 * K) +
    2048 + 992 * K + 160000 * K ^ 2
  let h := min (1 / 4 : Real) (1 / (8 * Real.sqrt B + 1))
  change 2 * (delta + D * Real.sqrt delta) < h →
    ∀ t ∈ Ioc s T, ∀ x, m62CurvatureSquared F c t x ≤ 2 / (t - s)
  intro hsmall tbad htbad xbad
  by_contra! hbad
  have hperiod : 0 < curvePeriod := Real.two_pi_pos
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hhquarter : h ≤ 1 / 4 := min_le_left _ _
  have hhcap : h ≤ 1 / (8 * Real.sqrt B + 1) := min_le_right _ _
  have hfour : 4 * Real.sqrt B * h ≤ 1 := by
    have hp := (le_div_iff₀ (show 0 < 8 * Real.sqrt B + 1 by positivity)).mp hhcap
    nlinarith only [hp, hh.le, mul_nonneg (Real.sqrt_nonneg B) hh.le]
  let Q : Set (Real × Real) := Icc s T ×ˢ Icc xbad (xbad + curvePeriod)
  let w : Real × Real → Real := fun z => (z.1 - s) * m62CurvatureSquared F c z.1 z.2
  let Z : Set (Real × Real) := {z ∈ Q | 2 ≤ w z}
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hw : ContinuousOn w Q := by
    have hq := (curvatureSquared_continuousOn F c hc).comp continuous_swap.continuousOn
      (show MapsTo Prod.swap Q (univ ×ˢ Icc a b) from
        fun z hz => ⟨mem_univ _, hs.trans hz.1.1, hz.1.2.trans hT⟩)
    exact (continuousOn_fst.sub continuousOn_const).mul hq
  have hZclosed : IsClosed Z := hQ.isClosed.isClosed_le continuousOn_const hw
  have hZ : IsCompact Z := hQ.of_isClosed_subset hZclosed (fun _ hz => hz.1)
  have hZne : Z.Nonempty := by
    refine ⟨(tbad, xbad), ⟨⟨⟨htbad.1.le, htbad.2⟩,
      ⟨le_rfl, le_add_of_nonneg_right hperiod.le⟩⟩, ?_⟩⟩
    have hm := (div_lt_iff₀ (sub_pos.mpr htbad.1)).mp hbad
    dsimp only [w]
    nlinarith only [hm]
  obtain ⟨z, hz, hmin⟩ := hZ.exists_isMinOn hZne continuousOn_fst
  let Tstar := z.1
  let xstar := z.2
  have hstar : Tstar ∈ Icc s T := hz.1.1
  have hthreshold : 2 ≤ (Tstar - s) * m62CurvatureSquared F c Tstar xstar := hz.2
  have hsstar : s < Tstar := by
    by_contra! h
    have heq : Tstar = s := le_antisymm h hstar.1
    rw [heq, sub_self, zero_mul] at hthreshold
    norm_num at hthreshold
  have hcap (t : Real) (ht : t ∈ Ioo s Tstar) (x : Real) :
      m62CurvatureSquared F c t x ≤ 2 / (t - s) := by
    by_contra! hlarge
    have ht' : t ∈ Ioo a b := ⟨hs.trans_lt ht.1, ht.2.trans_le (hstar.2.trans hT)⟩
    obtain ⟨y, hy, heq⟩ := (curvatureSquared_periodic F c hc ht').exists_mem_Ico hperiod x xbad
    have hyZ : (t, y) ∈ Z := by
      refine ⟨⟨⟨ht.1.le, ht.2.le.trans hstar.2⟩, ⟨hy.1, hy.2.le⟩⟩, ?_⟩
      rw [heq] at hlarge
      have hm := (div_lt_iff₀ (sub_pos.mpr ht.1)).mp hlarge
      dsimp only [w]
      nlinarith only [hm]
    have hminimal : Tstar ≤ t := hmin hyZ
    exact (not_le.mpr ht.2) hminimal
  let u := Tstar - s
  have hu : 0 < u := sub_pos.mpr hsstar
  have htimeStar : u ≤ delta * r ^ 2 := (sub_le_sub_right hstar.2 s).trans hTime
  have hr2 : r ^ 2 ≤ 1 := by nlinarith only [hr.le, hr1]
  have huDelta : u ≤ delta := htimeStar.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr2 hd.le)
  have hu1 : u ≤ 1 := huDelta.trans hd1
  have hsqrt : Real.sqrt u ≤ Real.sqrt delta * r := by
    simpa only [Real.sqrt_mul hd.le, Real.sqrt_sq hr.le] using Real.sqrt_le_sqrt htimeStar
  have hsqrtR : Real.sqrt u ≤ r := by
    have hdroot : Real.sqrt delta ≤ 1 := by
      nlinarith only [Real.sq_sqrt hd.le, Real.sqrt_nonneg delta, hd1]
    exact hsqrt.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hdroot hr.le)
  have hglobal (t : Real) (ht : t ∈ Icc s Tstar) :
      m62Length F c t ≤ E ∧ m62TotalCurvature F c t ≤ E :=
    hGlobal t ⟨ht.1, ht.2.trans hstar.2⟩
  have hsclosed : s ∈ Icc a b := ⟨hs, hsT.le.trans hT⟩
  have htclosed : Tstar ∈ Icc a b := ⟨hs.trans hsstar.le, hstar.2.trans hT⟩
  have hzero : m63ArcLength F c s xstar xstar ≤ r / 2 := by
    simp only [m63ArcLength, intervalIntegral.integral_same]
    positivity
  obtain ⟨lo, mid, hi, hlo, _hxm, _hmx, hhi, hper, _hleft, _hright,
    hwhole, _hinnerLeft, _hinnerRight⟩ :=
    m63ArcLength_exists_centered_enlargement F c hc hsclosed hr hLength le_rfl
      (le_add_of_nonneg_right hperiod.le) hzero
  have horder : lo ≤ hi := hlo.trans hhi
  have hL (t : Real) (ht : t ∈ Ioo s Tstar) :
      m63ArcLength F c t lo hi ≤ Real.exp K * r := by
    have ht' : t ∈ Icc a b := ⟨hs.trans ht.1.le, ht.2.le.trans htclosed.2⟩
    have hage : t - s ≤ 1 := (sub_le_sub_right ht.2.le s).trans hu1
    have he : Real.exp (K * (t - s)) ≤ Real.exp K := Real.exp_le_exp.mpr (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hage hK)
    calc
      _ ≤ m63ArcLength F c s lo hi * Real.exp (K * (t - s)) :=
        m63ArcLength_le_mul_exp F c hc hBounds horder hsclosed ht' ht.1.le
      _ = r * Real.exp (K * (t - s)) := by rw [hwhole]
      _ ≤ r * Real.exp K := mul_le_mul_of_nonneg_left he hr.le
      _ = Real.exp K * r := mul_comm _ _
  have hturn (t : Real) (ht : t ∈ Ioo s Tstar) :
      m63ArcTotalCurvature F c t lo hi ≤ E :=
    (m63ArcTotalCurvature_le_total F c hc horder hper
      ⟨hs.trans ht.1.le, ht.2.le.trans htclosed.2⟩).trans
      (hglobal t (Ioo_subset_Icc_self ht)).2
  have hloss := m63ArcLength_backward_loss F c hc hBounds hK horder hs htclosed.2 hsstar
    hE hL hturn (fun t ht x _ => hcap t ht x)
    (show Tstar ∈ Icc s Tstar from ⟨hsstar.le, le_rfl⟩)
  rw [hwhole] at hloss
  have hlossBound : K * (Real.exp K * r) * u + 2 * Real.sqrt 2 * E * Real.sqrt u ≤ r / 20 := by
    calc
      _ ≤ K * (Real.exp K * r) * delta + 2 * Real.sqrt 2 * E * (Real.sqrt delta * r) :=
        add_le_add (mul_le_mul_of_nonneg_left huDelta (by positivity))
          (mul_le_mul_of_nonneg_left hsqrt (by positivity))
      _ = (K * Real.exp K * delta + 2 * Real.sqrt 2 * E * Real.sqrt delta) * r := by ring
      _ ≤ (1 / 20 : Real) * r := mul_le_mul_of_nonneg_right hLoss hr.le
      _ = r / 20 := by ring
  have htotal : 19 * r / 20 ≤ m62Length F c Tstar := by
    have hle := m63ArcLength_le_length F c hc horder hper htclosed
    change r ≤ m63ArcLength F c Tstar lo hi + K * (Real.exp K * r) * u +
      2 * Real.sqrt 2 * E * Real.sqrt u at hloss
    linarith only [hloss, hlossBound, hle]
  have hsmallLength : h * Real.sqrt u ≤ r / 4 := by
    have hm := mul_le_mul hhquarter hsqrtR (Real.sqrt_nonneg u) (by norm_num : (0 : Real) ≤ 1 / 4)
    linarith only [hm]
  obtain ⟨_, sigma, hformula, _, _, _, hpos, _, hshift, _⟩ :=
    M63.exists_c2_unit_speed_parameter F (fun x => c x Tstar) Tstar
      (hc.periodic Tstar htclosed) (hc.spatial_regular Tstar htclosed) (hc.immersed Tstar htclosed)
  have hmono : StrictMono (sigma : Real → Real) := strictMono_of_deriv_pos hpos
  have hv : Continuous (curveSpeed F c Tstar) :=
    (speed_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, htclosed⟩)
  have hk : Continuous (m62Curvature F c Tstar) :=
    (curvature_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, htclosed⟩)
  have hprimitive (x y : Real) : m63ArcLength F c Tstar x y = sigma y - sigma x := by
    rw [hformula y, hformula x]
    exact (intervalIntegral.integral_interval_sub_left
      (hv.intervalIntegrable 0 y) (hv.intervalIntegrable 0 x)).symm
  let endpoint := sigma.symm (sigma xstar + h * Real.sqrt u)
  have hend : sigma endpoint = sigma xstar + h * Real.sqrt u := sigma.apply_symm_apply _
  have hxe : xstar ≤ endpoint := hmono.le_iff_le.mp (by
    rw [hend]
    exact le_add_of_nonneg_right (mul_nonneg hh.le (Real.sqrt_nonneg u)))
  have hperiodEnd : endpoint ≤ xstar + curvePeriod := hmono.le_iff_le.mp (by
    have hshift' : sigma (xstar + curvePeriod) = sigma xstar + m62Length F c Tstar := hshift xstar
    rw [hend, hshift']
    linarith only [hsmallLength, htotal, hr])
  have hlen : m63ArcLength F c Tstar xstar endpoint = h * Real.sqrt u := by
    rw [hprimitive, hend]
    ring
  have hosc := m63CurvatureSquared_closed_oscillation_of_inverse_age F c hc hK hBounds
    hRiemann hSecond hs hsstar htclosed.2 hu1 hcap
  have hqstar : 2 / u ≤ m62CurvatureSquared F c Tstar xstar :=
    (div_le_iff₀ hu).mpr (by simpa only [mul_comm] using hthreshold)
  have hpoint (y : Real) (hy : y ∈ Icc xstar endpoint) :
      1 / Real.sqrt u ≤ m62Curvature F c Tstar y := by
    have hprefix : m63ArcLength F c Tstar xstar y ≤ h * Real.sqrt u := by
      rw [← hlen]
      exact intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
        (Eventually.of_forall (speed_nonneg F c Tstar)) (hv.intervalIntegrable _ _)
    have ho : |m62CurvatureSquared F c Tstar y - m62CurvatureSquared F c Tstar xstar| ≤
        (4 * Real.sqrt B / (u * Real.sqrt u)) * m63ArcLength F c Tstar xstar y :=
      hosc xstar y hy.1
    have hoscSmall :
        |m62CurvatureSquared F c Tstar y - m62CurvatureSquared F c Tstar xstar| ≤ 1 / u := by
      calc
        _ ≤ (4 * Real.sqrt B / (u * Real.sqrt u)) * m63ArcLength F c Tstar xstar y := ho
        _ ≤ (4 * Real.sqrt B / (u * Real.sqrt u)) * (h * Real.sqrt u) :=
          mul_le_mul_of_nonneg_left hprefix (by positivity)
        _ = 4 * Real.sqrt B * h / u := by
          field_simp [(Real.sqrt_pos.mpr hu).ne']
        _ ≤ 1 / u := div_le_div_of_nonneg_right hfour hu.le
    have hq : 1 / u ≤ m62CurvatureSquared F c Tstar y := by
      have hl := (abs_le.mp hoscSmall).1
      have htwo : 2 / u = 1 / u + 1 / u := by ring
      linarith only [hl, hqstar, htwo]
    have hroot := Real.sqrt_le_sqrt hq
    change 1 / Real.sqrt u ≤ Real.sqrt (m62CurvatureSquared F c Tstar y)
    simpa only [Real.sqrt_div (by norm_num : (0 : Real) ≤ 1), Real.sqrt_one] using hroot
  have hturnLower : h ≤ m63ArcTotalCurvature F c Tstar xstar endpoint := by
    have hb := intervalIntegral.integral_mono_on (μ := volume) hxe
      ((hv.intervalIntegrable xstar endpoint).const_mul (1 / Real.sqrt u))
      ((hk.mul hv).intervalIntegrable xstar endpoint)
      (fun y hy => mul_le_mul_of_nonneg_right (hpoint y hy) (speed_nonneg F c Tstar y))
    rw [intervalIntegral.integral_const_mul] at hb
    change (1 / Real.sqrt u) * m63ArcLength F c Tstar xstar endpoint ≤
      m63ArcTotalCurvature F c Tstar xstar endpoint at hb
    rw [hlen] at hb
    have heq : (1 / Real.sqrt u) * (h * Real.sqrt u) = h := by
      field_simp [(Real.sqrt_pos.mpr hu).ne']
    rwa [heq] at hb
  have htransport := m63SmallSubarcs_transport_of_curvature_bound F c hc hK hE hBounds
    hP1 hP2 psi hpsi hRange hPlateau hSupport hFirst hSecondPsi hs hsstar htclosed.2
    hr hr1 hd hd1 htimeStar hLength hglobal hSmall hcap hLoss hExp
  have hturnUpper : m63ArcTotalCurvature F c Tstar xstar endpoint ≤
      2 * (delta + D * Real.sqrt delta) :=
    htransport Tstar ⟨hsstar.le, le_rfl⟩ xstar endpoint hxe hperiodEnd
      (by rw [hlen]; linarith only [hsmallLength, hr])
  linarith only [hturnLower, hturnUpper, hsmall]

end PoincareConjecture
