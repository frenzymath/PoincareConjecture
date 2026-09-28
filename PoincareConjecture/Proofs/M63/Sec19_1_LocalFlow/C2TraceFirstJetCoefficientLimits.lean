import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceCurvatureSecondSpatial
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddingBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TracePeriodicCurvature
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceEmbeddedEquation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedGradient
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1EmbeddingPushforward
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackRicciRegularity
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicDerivativeConvergence
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.SecondJetBound
import PoincareConjecture.Proofs.M04.ScalarHessian











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)

set_option maxHeartbeats 800000 in




theorem exists_normalFirstJet_normalizationDerivative_limits [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (c : ℕ → ℝ → ℝ → M) (hc : ∀ j, M62ShrinkingCurve F (c j))
    {Rcap m0 V0 : ℝ} (hRcap : 0 ≤ Rcap) (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    (vinit : ℕ → ℝ) (hvinit : ∀ j, vinit j ∈ Icc m0 V0)
    (hinitial : ∀ j x, curveSpeed F (c j) a x = vinit j)
    (hcurv : ∀ j t, t ∈ Ioo a b → ∀ x, m62CurvatureSquared F (c j) t x ≤ Rcap)
    {t : ℝ} (ht : t ∈ Ioo a b)
    (Rn Sn Hn : ℕ → X) (Vn : ℕ → XR) (r s h : X) (v : XR)
    (hR : Tendsto Rn atTop (𝓝 r)) (hS : Tendsto Sn atTop (𝓝 s))
    (hH : Tendsto Hn atTop (𝓝 h)) (hV : Tendsto Vn atTop (𝓝 v))
    (hRrep : ∀ j (x : ℝ), Rn j (x : AddCircle curvePeriod) = e (c j x t))
    (hSrep : ∀ j (x : ℝ), Sn j (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (spatialUnitTangent F (c j) t x))
    (hHrep : ∀ j (x : ℝ), Hn j (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x))
    (hVrep : ∀ j (x : ℝ), Vn j (x : AddCircle curvePeriod) = curveSpeed F (c j) t x)
    (hrU : ∀ z, r z ∈ U) :
    let B := fun z p q => coordinateHessian (F.connection t) e (ρ z)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z q)
    let A := fun z : W × (W × W) =>
      (F.connection t).ricci (ρ z.1)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.1) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.1) +
      (F.metric t).inner (ρ z.1)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.2) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.2)
    ∃ (Dn J1n : ℕ → X) (Bn : ℕ → XR) (dh j1 : X) (b0 : XR),
      (∀ j (x : ℝ), HasDerivAt (fun y : ℝ => Hn j (y : AddCircle curvePeriod))
        (Dn j (x : AddCircle curvePeriod)) x) ∧
      (∀ j (x : ℝ), J1n j (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m63CurvatureJet F (c j) 1 t x)) ∧
      (∀ j (x : ℝ), Bn j (x : AddCircle curvePeriod) = deriv (fun y =>
        m62TangentRicci F (c j) t y + m62CurvatureSquared F (c j) t y) x) ∧
      Tendsto Dn atTop (𝓝 dh) ∧ Tendsto J1n atTop (𝓝 j1) ∧ Tendsto Bn atTop (𝓝 b0) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => h (y : AddCircle curvePeriod))
        (dh (x : AddCircle curvePeriod)) x) ∧
      ∀ z, 0 < v z ∧ j1 z = (v z)⁻¹ • dh z - B (r z) (s z) (h z) ∧
        b0 z = fderiv ℝ A (r z, s z, h z)
          (v z • s z, v z • (B (r z) (s z) (s z) + h z), dh z) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  let B : W → W → W → W := fun z p q => coordinateHessian (F.connection t) e (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z q)
  let A := fun z : W × (W × W) =>
    (F.connection t).ricci (ρ z.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.1) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.1) +
    (F.metric t).inner (ρ z.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.2) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2.2)
  have hab : a < b := ht.1.trans ht.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  let Hspan := b - a
  have hHspan : 0 < Hspan := sub_pos.mpr hab
  obtain ⟨K, hK, hBounds, hRm, hRic2⟩ := m63Exists_firstJet_ambient_bounds F hcompact
  let A1 := 14 * Rcap + 10 * K + 1
  let G1 := 4 * Rcap ^ 3 + 2 * Rcap * K * (7 * Rcap + 6) + (K * (46 * Rcap + 32)) ^ 2
  let lam := 1 + A1 * Hspan
  let D0 := 4 * Rcap ^ 2 + m62C0 K K K * (2 * Rcap + 1)
  let D := Hspan * G1 + lam * D0
  let C1 := lam * Rcap + D * Hspan
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hG1 : 0 ≤ G1 := by dsimp only [G1]; positivity
  have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0, m62C0]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC1 : 0 ≤ C1 := by dsimp only [C1]; positivity
  let J := Real.sqrt C1
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  have hjet (j : ℕ) (u : ℝ) (hu : u ∈ Ioo a b) (x : ℝ) :
      (F.metric u).tangentNorm (c j x u) (m63CurvatureJet F (c j) 1 u x) ≤
        J / Real.sqrt (u - a) := by
    have hage : 0 < u - a := sub_pos.mpr hu.1
    have hageH : u - a ≤ Hspan := sub_le_sub_right hu.2.le a
    have hb := m63FirstJetSquared_short_time_bound F (c j) (hc j) hK hRcap
      hBounds hRm hRic2 (hcurv j) hHspan.le x u hu hageH
    change m63CurvatureJetSquared F (c j) 1 u x ≤ lam * Rcap / (u - a) + D at hb
    have hco : lam * Rcap / (u - a) + D ≤ C1 / (u - a) := by
      rw [div_add' _ _ _ hage.ne']
      apply div_le_div_of_nonneg_right _ hage.le
      dsimp only [C1]
      nlinarith [mul_le_mul_of_nonneg_left hageH hD]
    have hs := Real.sqrt_le_sqrt (hb.trans hco)
    rw [Real.sqrt_div hC1] at hs
    exact hs
  let Vcap := V0 * Real.exp ((K + Rcap) * Hspan)
  let Vmin := m0 * Real.exp (-(K + Rcap) * Hspan)
  have hVcap : 0 ≤ Vcap := mul_nonneg (hm0.le.trans hmV) (Real.exp_pos _).le
  have hVmin : 0 < Vmin := mul_pos hm0 (Real.exp_pos _)
  have hspeed (j : ℕ) (u : ℝ) (hu : u ∈ Icc a b) (x : ℝ) :
      Vmin ≤ curveSpeed F (c j) u x ∧ curveSpeed F (c j) u x ≤ Vcap := by
    have hv := curveSpeed_exp_bounds F (c j) (hc j) hBounds x
      (fun w hw => hcurv j w hw x) ha hu hu.1
    rw [hinitial] at hv
    constructor
    · apply le_trans _ hv.1
      apply mul_le_mul (hvinit j).1 _ (Real.exp_pos _).le (hm0.le.trans (hvinit j).1)
      apply Real.exp_le_exp.mpr
      dsimp only [Hspan]
      nlinarith [mul_le_mul_of_nonneg_left hu.2 (add_nonneg hK hRcap)]
    · apply hv.2.trans
      exact mul_le_mul (hvinit j).2
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hu.2 a) (add_nonneg hK hRcap)))
        (Real.exp_pos _).le (hm0.le.trans hmV)
  have hvpos (z : AddCircle curvePeriod) : 0 < v z := by
    have hvz := (continuous_eval_const z).tendsto v |>.comp hV
    have hlow : ∀ j, Vmin ≤ Vn j z := by
      intro j
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      rw [hVrep]
      exact (hspeed j t ht' x).1
    exact hVmin.trans_le (ge_of_tendsto hvz (Eventually.of_forall hlow))
  have hVnpos (j : ℕ) (z : AddCircle curvePeriod) : 0 < Vn j z := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hVrep]
    exact speed_pos F (c j) (hc j) ht' x
  let Gcap := Vcap ^ 2 * ((K + 2 * K * Real.sqrt Rcap) * Hspan +
    4 * Real.sqrt Rcap * J * Real.sqrt Hspan)
  have hGcap : 0 ≤ Gcap := by dsimp only [Gcap]; positivity
  have hgrad (j : ℕ) (x : ℝ) : |deriv (curveSpeed F (c j) t) x| ≤ Gcap := by
    have hb := curveSpeed_spatial_abs_bound F (c j) (hc j) hK hRcap hJ
      (hm0.trans_le (hvinit j).1) hBounds (hinitial j) (hcurv j) (hjet j) ht' x
    apply hb.trans
    have hvj : 0 ≤ vinit j := hm0.le.trans (hvinit j).1
    have hage : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
    have hageH : t - a ≤ Hspan := sub_le_sub_right ht.2.le a
    have hvExp : 0 ≤ vinit j * Real.exp ((K + Rcap) * Hspan) :=
      mul_nonneg hvj (Real.exp_pos _).le
    have hvExpLe : vinit j * Real.exp ((K + Rcap) * Hspan) ≤ Vcap :=
      mul_le_mul_of_nonneg_right (hvinit j).2 (Real.exp_pos _).le
    change _ ≤ Vcap ^ 2 * ((K + 2 * K * Real.sqrt Rcap) * Hspan +
      4 * Real.sqrt Rcap * J * Real.sqrt Hspan)
    exact mul_le_mul (pow_le_pow_left₀ hvExp hvExpLe 2)
      (add_le_add (mul_le_mul_of_nonneg_left hageH (by positivity))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hageH) (by positivity)))
      (by positivity) (sq_nonneg _)
  obtain ⟨C2, hC2, hsecond⟩ := m63SecondJetSquared_bound_of_curvature_bound F
    hcompact hRcap (sub_pos.mpr ht.1)
  have hjet2 (j : ℕ) (x : ℝ) :
      (F.metric t).tangentNorm (c j x t) (m63CurvatureJet F (c j) 2 t x) ≤ Real.sqrt C2 :=
    Real.sqrt_le_sqrt (hsecond (c j) (hc j) (hcurv j) x t ht le_rfl)
  have hk (j : ℕ) (x : ℝ) : m62Curvature F (c j) t x ≤ Real.sqrt Rcap :=
    Real.sqrt_le_sqrt (hcurv j t ht x)
  obtain ⟨E1, E2, E3, ⟨hE1, hE2, hE3⟩, hE⟩ :=
    exists_uniform_embedding_derivative_bounds F hcompact he
  let u1 := J / Real.sqrt (t - a)
  let L0 := Gcap * (E2 * Real.sqrt Rcap + E1 * u1) + Vcap ^ 2 *
    (E3 * Real.sqrt Rcap + E2 * (Real.sqrt Rcap) ^ 2 + 2 * E2 * u1 + E1 * Real.sqrt C2)
  have hu1 : 0 ≤ u1 := div_nonneg hJ (Real.sqrt_nonneg _)
  have hL0 : 0 ≤ L0 :=
    add_nonneg
      (mul_nonneg hGcap (add_nonneg (mul_nonneg hE2 (Real.sqrt_nonneg _))
        (mul_nonneg hE1 hu1)))
      (mul_nonneg (sq_nonneg _) (add_nonneg (add_nonneg
        (add_nonneg (mul_nonneg hE3 (Real.sqrt_nonneg _))
          (mul_nonneg hE2 (sq_nonneg _)))
        (mul_nonneg (mul_nonneg (by norm_num) hE2) hu1))
        (mul_nonneg hE1 (Real.sqrt_nonneg _))))
  have hsecondOrd (j : ℕ) (x : ℝ) :
      ‖deriv (deriv (fun y => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j y t)
        (m62CurvatureVector F (c j) t y) : W))) x‖ ≤ L0 := by
    have hb := embeddedCurvature_second_spatial_derivative_bound F (c j) (hc j) he ht x
      hE1 hE2 hE3 (fun Y => (hE t ht' (c j x t) Y 0 0).1)
      (fun Y Z => (hE t ht' (c j x t) Y Z 0).2.1)
      (fun Y Z Q => (hE t ht' (c j x t) Y Z Q).2.2)
    apply hb.trans
    have hk0 : 0 ≤ m62Curvature F (c j) t x := Real.sqrt_nonneg _
    have hj10 : 0 ≤ (F.metric t).tangentNorm (c j x t)
        (m63CurvatureJet F (c j) 1 t x) := Real.sqrt_nonneg _
    have hj20 : 0 ≤ (F.metric t).tangentNorm (c j x t)
        (m63CurvatureJet F (c j) 2 t x) := Real.sqrt_nonneg _
    have hv0 := (speed_pos F (c j) (hc j) ht' x).le
    have hsmall0 := add_nonneg (mul_nonneg hE2 hk0) (mul_nonneg hE1 hj10)
    have hsmall := add_le_add
      (mul_le_mul_of_nonneg_left (hk j x) hE2)
      (mul_le_mul_of_nonneg_left (hjet j t ht x) hE1)
    have hlarge0 := add_nonneg
      (add_nonneg (add_nonneg (mul_nonneg hE3 hk0)
        (mul_nonneg hE2 (sq_nonneg (m62Curvature F (c j) t x))))
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE2) hj10))
      (mul_nonneg hE1 hj20)
    have hlarge := add_le_add
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hk j x) hE3)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0 (hk j x) 2) hE2))
        (mul_le_mul_of_nonneg_left (hjet j t ht x)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hE2)))
      (mul_le_mul_of_nonneg_left (hjet2 j x) hE1)
    exact add_le_add (mul_le_mul (hgrad j x) hsmall hsmall0 hGcap)
      (mul_le_mul (pow_le_pow_left₀ hv0 (hspeed j t ht' x).2 2)
        hlarge hlarge0 (sq_nonneg _))
  have hdata (j : ℕ) : ∃ Dn DDn : X,
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => Hn j (y : AddCircle curvePeriod))
        (Dn (x : AddCircle curvePeriod)) x) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => Dn (y : AddCircle curvePeriod))
        (DDn (x : AddCircle curvePeriod)) x) ∧
      ∀ x : ℝ, ‖DDn (x : AddCircle curvePeriod)‖ ≤ L0 := by
    obtain ⟨Hj, Dj, DDj, _Tj, _hHj, _hDj, _hDDj, _hTj, hHjrep, _hDjrep,
      hDDjrep, _hTjrep, hd, hdd, _hdtime⟩ :=
      exists_periodic_embeddedCurvature_restart_data F (c j) hab (hc j) he
    have heq : Hn j = Hj t := by
      apply ContinuousMap.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      rw [hHrep, hHjrep t ht']
    refine ⟨Dj t, DDj t, ?_, hdd t ht, ?_⟩
    · rw [heq]
      exact hd t ht
    · intro x
      rw [hDDjrep t ht]
      simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
        iteratedDeriv_one, iteratedDeriv_zero] using hsecondOrd j x
  choose Dn DDn hDn hDDn hDDbound using hdata
  have hLip (j : ℕ) : LipschitzWith (⟨L0, hL0⟩ : ℝ≥0)
      (fun x : ℝ => Dn j (x : AddCircle curvePeriod)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hDDn j x).differentiableAt)
    intro x
    change ‖deriv (fun y : ℝ => Dn j (y : AddCircle curvePeriod)) x‖ ≤ L0
    rw [(hDDn j x).deriv]
    exact hDDbound j x
  obtain ⟨dh, hDlim, hdh⟩ := exists_periodic_derivative_limit Hn Dn h hDn hLip hH
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hBval (p : M) (Y Z : TangentSpace (𝓡 n) p) :
      B (e p) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p Y) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p Z) =
        coordinateHessian (F.connection t) e p Y Z := by
    dsimp only [B]
    rw [hleft, hleft, hρe]
  have hRder (j : ℕ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => Rn j (y : AddCircle curvePeriod))
        (Vn j (x : AddCircle curvePeriod) • Sn j (x : AddCircle curvePeriod)) x := by
    have hd := (c2ShrinkingCurve_embedded_closed_data (m63C2_of_m62 (hc j)) he).2.1 t ht' x
    have hv := (speed_pos F (c j) (hc j) ht' x).ne'
    have hvel : curveVelocity (fun y => c j y t) x =
        curveSpeed F (c j) t x • spatialUnitTangent F (c j) t x := by
      simp only [spatialUnitTangent, smul_smul, mul_inv_cancel₀ hv, one_smul]
    rw [hvel, map_smul] at hd
    rw [hVrep, hSrep]
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (hRrep j))
  have hSder (j : ℕ) (x : ℝ) :
      HasDerivAt (fun y : ℝ => Sn j (y : AddCircle curvePeriod))
        (Vn j (x : AddCircle curvePeriod) •
          (B (Rn j (x : AddCircle curvePeriod)) (Sn j (x : AddCircle curvePeriod))
            (Sn j (x : AddCircle curvePeriod)) + Hn j (x : AddCircle curvePeriod))) x := by
    let vj := curveSpeed F (c j) t x
    let Sj := spatialUnitTangent F (c j) t x
    have hv : vj ≠ 0 := (speed_pos F (c j) (hc j) ht' x).ne'
    have hspace := (m63C2_of_m62 (hc j)).spatial_regular t ht'
    have himm := (hc j).immersed t ht'
    have hd := hasDerivAt_embedding_pushforward_of_contMDiffAt_one (F.connection t) he
      ((hspace.of_le (by norm_num)) x) (spatialUnitTangent F (c j) t)
      ((unitTangent_contMDiff_of_c2 F (c j) hspace himm) x)
    have hvel : curveVelocity (fun y => c j y t) x = vj • Sj := by
      dsimp only [Sj, spatialUnitTangent]
      rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
    have hcov : rampHorizontalCovariantDerivative (F.connection t) (fun y => c j y t)
        (spatialUnitTangent F (c j) t) x = vj • m62CurvatureVector F (c j) t x := by
      change _ = vj • (vj⁻¹ • _)
      rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
    have hscale : coordinateHessian (F.connection t) e (c j x t) (vj • Sj) Sj =
        vj • coordinateHessian (F.connection t) e (c j x t) Sj Sj := by
      ext k
      have hek : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun p => e p k) :=
        (EuclideanSpace.proj k).contDiff.contMDiff.comp he
      obtain ⟨Q, hQ⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection t) hek).1 (c j x t)
      have hu (Y : TangentSpace (𝓡 n) (c j x t)) :
          Function.update ![Sj, Sj] 0 Y = ![Y, Sj] := by
        ext k
        fin_cases k <;> simp [Function.update]
      change (F.connection t).hessian (fun p => e p k) (c j x t) (vj • Sj) Sj =
        vj * (F.connection t).hessian (fun p => e p k) (c j x t) Sj Sj
      simpa only [hu, ← hQ, smul_eq_mul] using! Q.map_update_smul ![Sj, Sj] 0 vj Sj
    change HasDerivAt _ (HAdd.hAdd (α := W) (β := W) (γ := W)
      (coordinateHessian (F.connection t) e (c j x t)
        (curveVelocity (fun y => c j y t) x) Sj)
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t)
        (rampHorizontalCovariantDerivative (F.connection t) (fun y => c j y t)
          (spatialUnitTangent F (c j) t) x))) x at hd
    rw [hvel, hcov, hscale, map_smul, ← smul_add] at hd
    rw [hVrep, hRrep, hSrep, hHrep, hBval]
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (hSrep j))
  have hJrep (j : ℕ) (x : ℝ) :
      (Vn j (x : AddCircle curvePeriod))⁻¹ • Dn j (x : AddCircle curvePeriod) -
        B (Rn j (x : AddCircle curvePeriod)) (Sn j (x : AddCircle curvePeriod))
          (Hn j (x : AddCircle curvePeriod)) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m63CurvatureJet F (c j) 1 t x) := by
    have hd := hasDerivAt_embeddedCurvature_spatial F (c j) (hc j) he ht x
    have heq := (hDn j x).unique
      (hd.congr_of_eventuallyEq (Eventually.of_forall (hHrep j)))
    rw [heq, hVrep, hRrep, hSrep, hHrep, hBval, smul_smul,
      inv_mul_cancel₀ (speed_pos F (c j) (hc j) ht' x).ne', one_smul, add_sub_cancel_right]
    rfl
  let Ω : Set (W × (W × W)) := U ×ˢ univ
  have hΩ : IsOpen Ω := hU.prod isOpen_univ
  have hAc : ContDiffOn ℝ ∞ A Ω := by
    have hRic : ContDiffOn ℝ ∞ (fun z : (ℝ × W) × W =>
        (F.connection z.1.1).ricci (ρ z.1.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2)) ((Icc a b ×ˢ U) ×ˢ univ) :=
      flow_pullback_ricci_contDiffOn F hU hρ
    have hmet : ContDiffOn ℝ ∞ (fun z : (ℝ × W) × W =>
        (F.metric z.1.1).inner (ρ z.1.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2)
          (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2)) ((Icc a b ×ˢ U) ×ˢ univ) :=
      (flow_pullback_metric_hessian_contDiffOn F hU hρ
        (f := fun _ => 0) contMDiff_const).1
    let ricciInput : W × (W × W) → (ℝ × W) × W := fun z => ((t, z.1), z.2.1)
    let metricInput : W × (W × W) → (ℝ × W) × W := fun z => ((t, z.1), z.2.2)
    have hRI : ContDiff ℝ ∞ ricciInput :=
      (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd.fst
    have hMI : ContDiff ℝ ∞ metricInput :=
      (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd.snd
    have hRI_mem : MapsTo ricciInput Ω ((Icc a b ×ˢ U) ×ˢ univ) :=
      fun z hz => ⟨⟨ht', hz.1⟩, mem_univ _⟩
    have hMI_mem : MapsTo metricInput Ω ((Icc a b ×ˢ U) ×ˢ univ) :=
      fun z hz => ⟨⟨ht', hz.1⟩, mem_univ _⟩
    exact (hRic.comp (f := ricciInput) hRI.contDiffOn hRI_mem).add
      (hmet.comp (f := metricInput) hMI.contDiffOn hMI_mem)
  have hDA : ContinuousOn (fderiv ℝ A) Ω :=
    hAc.continuousOn_fderiv_of_isOpen hΩ (by simp)
  let Z := (U × (W × W)) × (Ioi (0 : ℝ) × W)
  let state : Z → W × (W × W) := fun z => (z.1.1, z.1.2)
  have hstate : Continuous state :=
    (continuous_subtype_val.comp continuous_fst.fst).prodMk continuous_fst.snd
  have hBC : ContinuousOn (fun z : (ℝ × W) × (W × W) =>
      coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)) ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).continuousOn
  let coefficientInput : U × (W × W) → (ℝ × W) × (W × W) :=
    fun z => ((t, z.1.1), z.2)
  have hInput : Continuous coefficientInput :=
    (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_snd
  have hInput_mem (z : U × (W × W)) :
      coefficientInput z ∈ ((Icc a b ×ˢ U) ×ˢ univ) :=
    ⟨⟨ht', z.1.2⟩, mem_univ _⟩
  have hBcont : Continuous (fun z : U × (W × W) => B z.1 z.2.1 z.2.2) :=
    hBC.comp_continuous (f := coefficientInput) hInput hInput_mem
  let diagonalInput : U × (W × W) → U × (W × W) := fun z => (z.1, z.2.1, z.2.1)
  have hDI : Continuous diagonalInput :=
    continuous_fst.prodMk (continuous_snd.fst.prodMk continuous_snd.fst)
  have hBdiag := hBcont.comp hDI
  let Jfun : Z → W := fun z => ((z.2.1 : ℝ))⁻¹ • z.2.2 - B z.1.1 z.1.2.1 z.1.2.2
  have hJfun : Continuous Jfun := by
    have hscalar : Continuous (fun z : Z => (z.2.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd.fst
    have hvector : Continuous (fun z : Z => z.2.2) := continuous_snd.snd
    have hvalue : Continuous (fun z : Z => B z.1.1 z.1.2.1 z.1.2.2) :=
      hBcont.comp (continuous_fst : Continuous (fun z : Z => z.1))
    exact ((hscalar.inv₀ (fun z => z.2.1.2.ne')).smul hvector).sub hvalue
  let Jmap : C(Z, W) := ⟨Jfun, hJfun⟩
  let Bmap : C(Z, ℝ) := ⟨fun z => fderiv ℝ A (state z)
      ((z.2.1 : ℝ) • z.1.2.1, (z.2.1 : ℝ) •
        (B z.1.1 z.1.2.1 z.1.2.1 + z.1.2.2), z.2.2),
    (hDA.comp_continuous hstate (fun z => ⟨z.1.1.2, mem_univ _⟩)).clm_apply
      (((continuous_subtype_val.comp continuous_snd.fst).smul continuous_fst.snd.fst).prodMk
        (((continuous_subtype_val.comp continuous_snd.fst).smul
          ((hBdiag.comp continuous_fst).add continuous_fst.snd.snd)).prodMk
          continuous_snd.snd))⟩
  have hRnU (j : ℕ) (z : AddCircle curvePeriod) : Rn j z ∈ U := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hRrep]
    exact heU (mem_range_self _)
  let R0 (j : ℕ) : C(AddCircle curvePeriod, U) :=
    ⟨fun z => ⟨Rn j z, hRnU j z⟩, (Rn j).continuous.subtype_mk _⟩
  let r0 : C(AddCircle curvePeriod, U) :=
    ⟨fun z => ⟨r z, hrU z⟩, r.continuous.subtype_mk _⟩
  let Vp (j : ℕ) : C(AddCircle curvePeriod, Ioi (0 : ℝ)) :=
    ⟨fun z => ⟨Vn j z, hVnpos j z⟩, (Vn j).continuous.subtype_mk _⟩
  let vp : C(AddCircle curvePeriod, Ioi (0 : ℝ)) :=
    ⟨fun z => ⟨v z, hvpos z⟩, v.continuous.subtype_mk _⟩
  let incU : C(U, W) := ⟨Subtype.val, continuous_subtype_val⟩
  let incV : C(Ioi (0 : ℝ), ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hR0 : Tendsto R0 atTop (𝓝 r0) :=
    (incU.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr hR
  have hVp : Tendsto Vp atTop (𝓝 vp) :=
    (incV.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr hV
  let bundle (q : (C(AddCircle curvePeriod, U) × (X × X)) ×
      (C(AddCircle curvePeriod, Ioi (0 : ℝ)) × X)) : C(AddCircle curvePeriod, Z) :=
    (q.1.1.prodMk (q.1.2.1.prodMk q.1.2.2)).prodMk (q.2.1.prodMk q.2.2)
  have hbundle : Continuous bundle := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_fst.fst.fst.eval continuous_snd).prodMk
      ((continuous_fst.fst.snd.fst.eval continuous_snd).prodMk
        (continuous_fst.fst.snd.snd.eval continuous_snd))).prodMk
      ((continuous_fst.snd.fst.eval continuous_snd).prodMk
        (continuous_fst.snd.snd.eval continuous_snd))
  let zn (j : ℕ) := bundle ((R0 j, Sn j, Hn j), Vp j, Dn j)
  let z0 := bundle ((r0, s, h), vp, dh)
  have hzn : Tendsto zn atTop (𝓝 z0) := (hbundle.tendsto _).comp
    ((hR0.prodMk_nhds (hS.prodMk_nhds hH)).prodMk_nhds (hVp.prodMk_nhds hDlim))
  refine ⟨Dn, fun j => Jmap.comp (zn j), fun j => Bmap.comp (zn j), dh,
    Jmap.comp z0, Bmap.comp z0, hDn, hJrep, ?_, hDlim,
    (Jmap.continuous_postcomp.tendsto _).comp hzn,
    (Bmap.continuous_postcomp.tendsto _).comp hzn, hdh,
    fun z => ⟨hvpos z, rfl, rfl⟩⟩
  intro j x
  have hactual : (fun y : ℝ => A (Rn j (y : AddCircle curvePeriod),
      Sn j (y : AddCircle curvePeriod), Hn j (y : AddCircle curvePeriod))) =
      fun y => m62TangentRicci F (c j) t y + m62CurvatureSquared F (c j) t y := by
    funext y
    dsimp only [A]
    rw [hRrep, hSrep, hHrep, hleft, hleft, hρe]
    rfl
  have hdiff := (hAc.contDiffAt (hΩ.mem_nhds
    (show (Rn j (x : AddCircle curvePeriod), Sn j (x : AddCircle curvePeriod),
      Hn j (x : AddCircle curvePeriod)) ∈ Ω from ⟨hRnU j _, mem_univ _⟩))).differentiableAt
        (by simp)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt x
    ((hRder j x).prodMk ((hSder j x).prodMk (hDn j x)))
  simp only [Function.comp_def] at hd
  rw [hactual] at hd
  exact hd.deriv.symm

end PoincareConjecture.M63
