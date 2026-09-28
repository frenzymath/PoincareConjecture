import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ShortTimeFirstJet
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLength
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalization
import PoincareConjecture.Proofs.M63.Adapters
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture

open M62

variable {n : Nat} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : Real}




theorem m63CurvatureSquared_closed_oscillation_of_inverse_age
    (F : RicciFlow n M (Icc a b)) (c : Real → Real → M)
    (hc : M62ShrinkingCurve F c) {K : Real} (hK : 0 ≤ K)
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
    {s T : Real} (hs : a ≤ s) (hsT : s < T) (hT : T ≤ b)
    (hAge : T - s ≤ 1)
    (hCurv : ∀ t ∈ Ioo s T, ∀ x,
      m62CurvatureSquared F c t x ≤ 2 / (t - s)) :
    let B := (272 + 17 * m62C0 K K K) * (114 + 10 * K) +
      2048 + 992 * K + 160000 * K ^ 2
    ∀ alpha beta : Real, alpha ≤ beta →
      |m62CurvatureSquared F c T beta - m62CurvatureSquared F c T alpha| ≤
        (4 * Real.sqrt B / ((T - s) * Real.sqrt (T - s))) *
          m63ArcLength F c T alpha beta := by
  let u := T - s
  let C0 := m62C0 K K K
  let B := (272 + 17 * C0) * (114 + 10 * K) + 2048 + 992 * K + 160000 * K ^ 2
  let l := s + 3 * u / 4
  let alphaTime := s + u / 4
  let R := 8 / u
  let lam := 1 + (14 * R + 10 * K + 1) * u
  let D0 := 4 * R ^ 2 + C0 * (2 * R + 1)
  let G := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
  have hu : 0 < u := sub_pos.mpr hsT
  have hu1 : u ≤ 1 := hAge
  have hu2 : u ^ 2 ≤ 1 := by nlinarith only [hu.le, hu1]
  have hu3 : u ^ 3 ≤ 1 := by
    calc
      u ^ 3 = u ^ 2 * u := by ring
      _ ≤ 1 * 1 := mul_le_mul hu2 hu1 hu.le zero_le_one
      _ = 1 := mul_one 1
  have hC0 : 0 ≤ C0 := by dsimp only [C0, m62C0]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
  have hsa : s < alphaTime := by dsimp only [alphaTime]; linarith only [hu]
  have halphaT : alphaTime < T := by dsimp only [alphaTime, u]; linarith only [hsT]
  have hlT : l < T := by dsimp only [l, u]; linarith only [hsT]
  have hsl : s < l := by dsimp only [l]; linarith only [hu]
  have hsub : Icc alphaTime T ⊆ Icc a b := fun t ht =>
    ⟨hs.trans (hsa.le.trans ht.1), ht.2.trans hT⟩
  let F' := m63RestrictClosedFlow F alphaTime T hsub halphaT
  have hc' : M62ShrinkingCurve F' c :=
    m63SmoothRestriction (m63SmoothClosed_iff_m62.mpr hc) alphaTime T hsub halphaT
  have hcurv' (t : Real) (ht : t ∈ Ioo alphaTime T) (x : Real) :
      m62CurvatureSquared F' c t x ≤ R := by
    have ht' : t ∈ Ioo s T := ⟨hsa.trans ht.1, ht.2⟩
    have hden : u / 4 ≤ t - s := by dsimp only [alphaTime] at ht; linarith only [ht.1]
    change m62CurvatureSquared F c t x ≤ R
    calc
      _ ≤ 2 / (t - s) := hCurv t ht' x
      _ ≤ 2 / (u / 4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = R := by dsimp only [R]; ring
  have hlamBound : lam ≤ 114 + 10 * K := by
    have heq : lam = 113 + (10 * K + 1) * u := by
      dsimp only [lam, R]
      field_simp
      ring
    rw [heq]
    have h := mul_le_mul_of_nonneg_left hu1 (show 0 ≤ 10 * K + 1 by positivity)
    linarith only [h]
  have hD0 : D0 ≤ (256 + 17 * C0) / u ^ 2 := by
    apply (le_div_iff₀ (pow_pos hu 2)).mpr
    have heq : D0 * u ^ 2 = 256 + C0 * (16 * u + u ^ 2) := by
      dsimp only [D0, R]
      field_simp
      ring
    rw [heq]
    have hpoly : 16 * u + u ^ 2 ≤ 17 := by linarith only [hu1, hu2]
    have h := mul_le_mul_of_nonneg_left hpoly hC0
    linarith only [h]
  have hG : u * G ≤ (2048 + 992 * K + 160000 * K ^ 2) / u ^ 2 := by
    apply (le_div_iff₀ (pow_pos hu 2)).mpr
    have heq : u * G * u ^ 2 = 2048 + 896 * K * u + 96 * K * u ^ 2 +
        K ^ 2 * (135424 * u + 23552 * u ^ 2 + 1024 * u ^ 3) := by
      dsimp only [G, R]
      field_simp
      ring
    rw [heq]
    have hfirst := mul_le_mul_of_nonneg_left hu1 (show 0 ≤ 896 * K by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ 96 * K by positivity)
    have hpoly : 135424 * u + 23552 * u ^ 2 + 1024 * u ^ 3 ≤ 160000 := by
      linarith only [hu1, hu2, hu3]
    have hthird := mul_le_mul_of_nonneg_left hpoly (sq_nonneg K)
    linarith only [hfirst, hsecond, hthird]
  have hq1 (t : Real) (ht : t ∈ Ioo l T) (x : Real) :
      m63CurvatureJetSquared F c 1 t x ≤ B / u ^ 2 := by
    have htlower : alphaTime < t := by dsimp only [alphaTime, l] at *; linarith only [ht.1, hu]
    have hage : u / 2 ≤ t - alphaTime := by
      dsimp only [alphaTime, l] at *
      linarith only [ht.1]
    have hageu : t - alphaTime ≤ u := by
      dsimp only [alphaTime, u]
      linarith only [ht.2, hsT]
    have hraw := m63FirstJetSquared_short_time_bound F' c hc' hK hR
      (m63RestrictAmbientBounds hBounds alphaTime T hsub halphaT)
      (fun r hr p v hv => hRiemann r (hsub hr) p v hv)
      (fun r hr p v hv => hSecond r (hsub hr) p v hv)
      hcurv' hu.le x t ⟨htlower, ht.2⟩ hageu
    change m63CurvatureJetSquared F c 1 t x ≤
      lam * R / (t - alphaTime) + (u * G + lam * D0) at hraw
    have hterm : lam * R / (t - alphaTime) ≤ 16 * (114 + 10 * K) / u ^ 2 := by
      calc
        _ ≤ lam * R / (u / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hlam hR) (by positivity) hage
        _ = 16 * lam / u ^ 2 := by dsimp only [R]; field_simp; ring
        _ ≤ 16 * (114 + 10 * K) / u ^ 2 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlamBound (by norm_num)) (sq_nonneg u)
    have hDterm : lam * D0 ≤ (114 + 10 * K) * (256 + 17 * C0) / u ^ 2 := by
      calc
        _ ≤ lam * ((256 + 17 * C0) / u ^ 2) := mul_le_mul_of_nonneg_left hD0 hlam
        _ ≤ (114 + 10 * K) * ((256 + 17 * C0) / u ^ 2) :=
          mul_le_mul_of_nonneg_right hlamBound (by positivity)
        _ = _ := by ring
    calc
      _ ≤ lam * R / (t - alphaTime) + (u * G + lam * D0) := hraw
      _ ≤ 16 * (114 + 10 * K) / u ^ 2 +
          ((2048 + 992 * K + 160000 * K ^ 2) / u ^ 2 +
            (114 + 10 * K) * (256 + 17 * C0) / u ^ 2) :=
        add_le_add hterm (add_le_add hG hDterm)
      _ = B / u ^ 2 := by dsimp only [B]; ring
  let C := 4 * Real.sqrt B / (u * Real.sqrt u)
  have hderiv (t : Real) (ht : t ∈ Ioo l T) (x : Real) :
      |deriv (m62CurvatureSquared F c t) x| ≤ C * curveSpeed F c t x := by
    have ht' : t ∈ Ioo a b := ⟨hs.trans_lt (hsl.trans ht.1), ht.2.trans_le hT⟩
    have htclosed := Ioo_subset_Icc_self ht'
    have hv : 0 < curveSpeed F c t x := speed_pos F c hc htclosed x
    have hden : u / 2 ≤ t - s := by dsimp only [l] at ht; linarith only [ht.1, hu]
    have hq0 : m62CurvatureSquared F c t x ≤ 4 / u := by
      calc
        _ ≤ 2 / (t - s) := hCurv t ⟨hsl.trans ht.1, ht.2⟩ x
        _ ≤ 2 / (u / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
        _ = 4 / u := by ring
    have hk : m62Curvature F c t x ≤ 2 / Real.sqrt u := by
      change Real.sqrt (m62CurvatureSquared F c t x) ≤ 2 / Real.sqrt u
      have h := Real.sqrt_le_sqrt hq0
      simpa only [Real.sqrt_div (by norm_num : (0 : Real) ≤ 4),
        show Real.sqrt 4 = 2 from by norm_num] using h
    have hj : (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
        Real.sqrt B / u := by
      change Real.sqrt (m63CurvatureJetSquared F c 1 t x) ≤ Real.sqrt B / u
      have h := Real.sqrt_le_sqrt (hq1 t ht x)
      simpa only [Real.sqrt_div hB, Real.sqrt_sq hu.le] using h
    let H := m63CurvatureJet F c 0 t x
    let J := m63CurvatureJet F c 1 t x
    have harc : m62ArcDerivative F c t (m62CurvatureSquared F c t) x =
        2 * (F.metric t).inner (c x t) H J := by
      have hHsmooth := M63.curvatureJet_joint_contMDiff F c hc 0
      have h := m63ArcDerivative_metric_pairing F c hc
        (fun z => m63CurvatureJet F c 0 z.2 z.1)
        (fun z => m63CurvatureJet F c 0 z.2 z.1) hHsmooth hHsmooth ht' x
      change m62ArcDerivative F c t (m62CurvatureSquared F c t) x =
        (F.metric t).inner (c x t) J H + (F.metric t).inner (c x t) H J at h
      rw [(F.metric t).symm (c x t) J H] at h
      linarith only [h]
    have hdx : curveSpeed F c t x * m62ArcDerivative F c t (m62CurvatureSquared F c t) x =
        deriv (m62CurvatureSquared F c t) x := by
      unfold m62ArcDerivative
      rw [← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    have hn (Z : TangentSpace (𝓡 n) (c x t)) : ‖Z‖ = (F.metric t).tangentNorm (c x t) Z := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    have hpair : |(F.metric t).inner (c x t) H J| ≤
        m62Curvature F c t x * (F.metric t).tangentNorm (c x t) J := by
      change |inner Real H J| ≤ _
      have hHN : (F.metric t).tangentNorm (c x t) H = m62Curvature F c t x := rfl
      simpa only [hn, hHN] using abs_real_inner_le_norm H J
    rw [← hdx, harc, abs_mul, abs_of_pos hv, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    calc
      _ ≤ curveSpeed F c t x * (2 *
          (m62Curvature F c t x * (F.metric t).tangentNorm (c x t) J)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair (by norm_num)) hv.le
      _ ≤ curveSpeed F c t x * (2 * ((2 / Real.sqrt u) * (Real.sqrt B / u))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul hk hj (Real.sqrt_nonneg _) (by positivity)) (by norm_num)) hv.le
      _ = C * curveSpeed F c t x := by dsimp only [C]; field_simp; ring
  change ∀ alpha beta : Real, alpha ≤ beta →
    |m62CurvatureSquared F c T beta - m62CurvatureSquared F c T alpha| ≤
      C * m63ArcLength F c T alpha beta
  intro alpha beta hab
  have hinter (t : Real) (ht : t ∈ Ioo l T) :
      |m62CurvatureSquared F c t beta - m62CurvatureSquared F c t alpha| ≤
        C * m63ArcLength F c t alpha beta := by
    have ht' : t ∈ Ioo a b := ⟨hs.trans_lt (hsl.trans ht.1), ht.2.trans_le hT⟩
    have hq : ContDiff Real ∞ (m62CurvatureSquared F c t) :=
      (curvatureSquared_contDiffOn F c hc).comp_contDiff
        (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht'⟩)
    have hv : Continuous (curveSpeed F c t) :=
      (speed_continuousOn F c hc).comp_continuous
        (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, Ioo_subset_Icc_self ht'⟩)
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le hab hq.continuous.continuousOn
      (hq.differentiable (by simp)).differentiableOn
      (Eventually.of_forall fun x _ => by simpa only [Real.norm_eq_abs] using hderiv t ht x)
      ((hv.intervalIntegrable alpha beta).const_mul C)
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul, m63ArcLength] using h
  have hqtime (x : Real) :
      ContinuousOn (fun t => m62CurvatureSquared F c t x) (Icc a b) :=
    (curvatureSquared_continuousOn F c hc).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨mem_univ _, ht⟩)
  have hsubLast : Icc l T ⊆ Icc a b := fun t ht =>
    ⟨hs.trans (hsl.le.trans ht.1), ht.2.trans hT⟩
  apply le_on_closure hinter
  · simpa only [closure_Ioo hlT.ne, Pi.sub_apply] using
      (((hqtime beta).sub (hqtime alpha)).abs.mono hsubLast)
  · simpa only [closure_Ioo hlT.ne, Pi.mul_apply, C] using!
      ((continuousOn_const.mul (m63ArcLength_continuousOn F c hc alpha beta)).mono hsubLast)
  · simpa only [closure_Ioo hlT.ne] using (show T ∈ Icc l T from ⟨hlT.le, le_rfl⟩)

end PoincareConjecture
