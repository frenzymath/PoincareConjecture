import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.UniformUpperCutoffJetBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_terminal_speed_jet_bounds
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {alpha tau T : ℝ} (haa : a ≤ alpha) (hat : alpha < tau)
    (htT : tau < T) (hTb : T ≤ b)
    {c : ℝ → ℝ → M}
    (hsmooth : ∀ s, s ∈ Ioo alpha T → M63SmoothShrinkingCurveOn F c (Icc alpha s))
    {R v0 : ℝ} (hR : 0 ≤ R) (hv0 : 0 < v0)
    (hinitial : ∀ x, curveSpeed F c alpha x = v0)
    (hcurv : ∀ t, t ∈ Ioo alpha T → ∀ x, m62CurvatureSquared F c t x ≤ R) :
    ∃ K J m V G J1 J2 : ℝ,
      0 ≤ K ∧ CurveEvolutionAmbientBounds F K K K ∧
      0 ≤ J ∧ 0 < m ∧ 0 ≤ V ∧ 0 ≤ G ∧ 0 ≤ J1 ∧ 0 ≤ J2 ∧
      (∀ t, t ∈ Ioo alpha T → ∀ x,
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
          J / Real.sqrt (t - alpha)) ∧
      (∀ t, t ∈ Ico alpha T → ∀ x,
        m ≤ curveSpeed F c t x ∧ curveSpeed F c t x ≤ V) ∧
      (∀ t, t ∈ Ico alpha T → ∀ x, |deriv (curveSpeed F c t) x| ≤ G) ∧
      (∀ t, t ∈ Ico tau T → ∀ x,
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤ J1 ∧
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 2 t x) ≤ J2) ∧
      ∀ t, t ∈ Ico alpha T → ∀ x,
        IntervalIntegrable
          (fun r => deriv (fun y =>
            m62TangentRicci F c r y + m62CurvatureSquared F c r y) x) volume alpha t ∧
        deriv (curveSpeed F c t) x = -curveSpeed F c t x *
          ∫ r in alpha..t, deriv (fun y =>
            m62TangentRicci F c r y + m62CurvatureSquared F c r y) x := by
  have haT : alpha < T := hat.trans htT
  let H := T - alpha
  have hH : 0 ≤ H := (sub_pos.mpr haT).le
  obtain ⟨K, hK, hBounds, hRm, hRc⟩ := m63Exists_firstJet_ambient_bounds F hcompact
  let A := 14 * R + 10 * K + 1
  let G0 := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
  let lam := 1 + A * H
  let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
  let D := H * G0 + lam * D0
  have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hG0 : 0 ≤ G0 := by dsimp only [G0]; positivity
  have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let J := Real.sqrt (lam * R + D * H)
  let m := v0 * Real.exp (-(K + R) * H)
  let V := v0 * Real.exp ((K + R) * H)
  let G := V ^ 2 * ((K + 2 * K * Real.sqrt R) * H +
    4 * Real.sqrt R * J * Real.sqrt H)
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  have hm : 0 < m := mul_pos hv0 (Real.exp_pos _)
  have hV : 0 ≤ V := (mul_pos hv0 (Real.exp_pos _)).le
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hsub (s : ℝ) (hs : s ∈ Ioo alpha T) : Icc alpha s ⊆ Icc a b :=
    fun t ht => ⟨haa.trans ht.1, ht.2.trans (hs.2.le.trans hTb)⟩
  let Fs (s : ℝ) (hs : s ∈ Ioo alpha T) :=
    m63RestrictClosedFlow F alpha s (hsub s hs) hs.1
  have hcs (s : ℝ) (hs : s ∈ Ioo alpha T) : M62ShrinkingCurve (Fs s hs) c :=
    m63SmoothRestriction (hsmooth s hs) alpha s Subset.rfl hs.1
  have hBs (s : ℝ) (hs : s ∈ Ioo alpha T) :
      CurveEvolutionAmbientBounds (Fs s hs) K K K :=
    m63RestrictAmbientBounds hBounds alpha s (hsub s hs) hs.1
  have hjetEq (s : ℝ) (hs : s ∈ Ioo alpha T) (i : ℕ) (t x : ℝ) :
      m63CurvatureJet (Fs s hs) c i t x = m63CurvatureJet F c i t x := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih =>
      change m62SpatialDerivative F c t (fun y => m63CurvatureJet (Fs s hs) c i t y) x =
        m62SpatialDerivative F c t (fun y => m63CurvatureJet F c i t y) x
      rw [show (fun y => m63CurvatureJet (Fs s hs) c i t y) =
        (fun y => m63CurvatureJet F c i t y) from funext ih]
  have hsqEq (s : ℝ) (hs : s ∈ Ioo alpha T) (i : ℕ) (t x : ℝ) :
      m63CurvatureJetSquared (Fs s hs) c i t x = m63CurvatureJetSquared F c i t x := by
    simp only [m63CurvatureJetSquared, hjetEq s hs]
    rfl
  have hcut (t : ℝ) (ht : t ∈ Ico alpha T) : ∃ s, s ∈ Ioo alpha T ∧ t < s := by
    refine ⟨(t + T) / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith [ht.1, ht.2]
  have hshort (t : ℝ) (ht : t ∈ Ioo alpha T) (x : ℝ) :
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
        J / Real.sqrt (t - alpha) := by
    obtain ⟨s, hs, hts⟩ := hcut t (Ioo_subset_Ico_self ht)
    have hage : 0 < t - alpha := sub_pos.mpr ht.1
    have hageH : t - alpha ≤ H := sub_le_sub_right ht.2.le alpha
    have hb := m63FirstJetSquared_short_time_bound (Fs s hs) c (hcs s hs) hK hR
      (hBs s hs) (fun r hr p w hw => hRm r (hsub s hs hr) p w hw)
      (fun r hr p w hw => hRc r (hsub s hs hr) p w hw)
      (fun r hr y => hcurv r ⟨hr.1, hr.2.trans hs.2⟩ y) hH x t ⟨ht.1, hts⟩ hageH
    change m63CurvatureJetSquared (Fs s hs) c 1 t x ≤ lam * R / (t - alpha) + D at hb
    rw [hsqEq s hs] at hb
    have hf : lam * R / (t - alpha) + D ≤ (lam * R + D * H) / (t - alpha) := by
      apply (le_div_iff₀ hage).mpr
      rw [add_mul, div_mul_cancel₀ _ hage.ne']
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hageH hD)
    change Real.sqrt (m63CurvatureJetSquared F c 1 t x) ≤
      Real.sqrt (lam * R + D * H) / Real.sqrt (t - alpha)
    exact (Real.sqrt_le_sqrt (hb.trans hf)).trans_eq
      (Real.sqrt_div (add_nonneg (mul_nonneg hlam hR) (mul_nonneg hD hH)) _)
  have hspeed (t : ℝ) (ht : t ∈ Ico alpha T) (x : ℝ) :
      m ≤ curveSpeed F c t x ∧ curveSpeed F c t x ≤ V := by
    obtain ⟨s, hs, hts⟩ := hcut t ht
    have hb := curveSpeed_exp_bounds (Fs s hs) c (hcs s hs) (hBs s hs) x
      (fun r hr => hcurv r ⟨hr.1, hr.2.trans hs.2⟩ x)
      (show alpha ∈ Icc alpha s from ⟨le_rfl, hs.1.le⟩)
      (show t ∈ Icc alpha s from ⟨ht.1, hts.le⟩) ht.1
    change curveSpeed F c alpha x * Real.exp (-(K + R) * (t - alpha)) ≤
        curveSpeed F c t x ∧ curveSpeed F c t x ≤
        curveSpeed F c alpha x * Real.exp ((K + R) * (t - alpha)) at hb
    rw [hinitial] at hb
    have hage : t - alpha ≤ H := sub_le_sub_right ht.2.le alpha
    have hexp := mul_le_mul_of_nonneg_left hage (add_nonneg hK hR)
    exact ⟨(mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hv0.le).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hv0.le)⟩
  have hgrad (t : ℝ) (ht : t ∈ Ico alpha T) (x : ℝ) :
      |deriv (curveSpeed F c t) x| ≤ G := by
    obtain ⟨s, hs, hts⟩ := hcut t ht
    have hb := curveSpeed_spatial_abs_bound (Fs s hs) c (hcs s hs) hK hR hJ hv0
      (hBs s hs) hinitial (fun r hr y => hcurv r ⟨hr.1, hr.2.trans hs.2⟩ y)
      (fun r hr y => by rw [hjetEq s hs]; exact hshort r ⟨hr.1, hr.2.trans hs.2⟩ y)
      (show t ∈ Icc alpha s from ⟨ht.1, hts.le⟩) x
    have hVsmall : v0 * Real.exp ((K + R) * (s - alpha)) ≤ V :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2.le alpha) (add_nonneg hK hR))) hv0.le
    have hage : t - alpha ≤ H := sub_le_sub_right ht.2.le alpha
    have hlin : 0 ≤ K + 2 * K * Real.sqrt R := by positivity
    have hroot : 0 ≤ 4 * Real.sqrt R * J := by positivity
    apply hb.trans
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hVsmall 2)
      (add_le_add (mul_le_mul_of_nonneg_left hage hlin)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hage) hroot))
      (add_nonneg (mul_nonneg hlin (sub_nonneg.mpr ht.1))
        (mul_nonneg hroot (Real.sqrt_nonneg _))) (sq_nonneg V)
  obtain ⟨C1, _hC1, hcap1⟩ := m63CurvatureJetSquared_bound_uniform_upper_cutoff F hcompact 1
    haa haT hTb hR (sub_pos.mpr hat)
  obtain ⟨C2, _hC2, hcap2⟩ := m63CurvatureJetSquared_bound_uniform_upper_cutoff F hcompact 2
    haa haT hTb hR (sub_pos.mpr hat)
  refine ⟨K, J, m, V, G, Real.sqrt C1, Real.sqrt C2, hK, hBounds, hJ, hm,
    hV, hG, Real.sqrt_nonneg _, Real.sqrt_nonneg _, hshort, hspeed, hgrad, ?_, ?_⟩
  · intro t ht x
    obtain ⟨s, hs, hts⟩ := hcut t ⟨hat.le.trans ht.1, ht.2⟩
    have hts' : t ∈ Ioo alpha s := ⟨hat.trans_le ht.1, hts⟩
    have hage : tau - alpha ≤ t - alpha := sub_le_sub_right ht.1 alpha
    have hc : ∀ r ∈ Ioo alpha s, ∀ y, m63CurvatureJetSquared F c 0 r y ≤ R :=
      fun r hr y => hcurv r ⟨hr.1, hr.2.trans hs.2⟩ y
    exact ⟨Real.sqrt_le_sqrt (hcap1 s hs.1 hs.2.le c (hsmooth s hs) hc t hts' hage x),
      Real.sqrt_le_sqrt (hcap2 s hs.1 hs.2.le c (hsmooth s hs) hc t hts' hage x)⟩
  · intro t ht x
    obtain ⟨s, hs, hts⟩ := hcut t ht
    have ht' : t ∈ Icc alpha s := ⟨ht.1, hts.le⟩
    have hformula := curveSpeed_spatial_derivative_integral (Fs s hs) c (hcs s hs)
      hK hR hJ hv0 (hBs s hs) hinitial
      (fun r hr y => hcurv r ⟨hr.1, hr.2.trans hs.2⟩ y)
      (fun r hr y => by rw [hjetEq s hs]; exact hshort r ⟨hr.1, hr.2.trans hs.2⟩ y) ht' x
    refine ⟨?_, hformula⟩
    let Q : ℝ × ℝ → ℝ := fun z =>
      m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1
    let Qx := M08.coordinatePartialS Q
    let B : ℝ → ℝ := fun r => V * (K + 2 * K * Real.sqrt R) +
      (2 * V * Real.sqrt R * J) * (r - alpha) ^ (-(1 / 2 : ℝ))
    have hopen : IsOpen (univ ×ˢ Ioo alpha s : Set (ℝ × ℝ)) :=
      isOpen_univ.prod isOpen_Ioo
    have hQ : ContDiffOn ℝ ∞ Q (univ ×ˢ Ioo alpha s) :=
      normalization_coefficient_contDiffOn (Fs s hs) c (hcs s hs)
    have hQx : ContDiffOn ℝ ∞ Qx (univ ×ˢ Ioo alpha s) :=
      M08.coordinatePartialS_contDiffOn hopen Q hQ
    have hdiff (r : ℝ) (hr : r ∈ Ioo alpha s) (y : ℝ) :
        HasDerivAt (fun y => Q (y, r)) (Qx (y, r)) y :=
      M08.coordinateSlice_fst_hasDerivAt Q (p := (y, r))
        ((hQ.contDiffAt (hopen.mem_nhds ⟨mem_univ _, hr⟩)).differentiableAt (by simp))
    have hcont : ContinuousOn (fun r => deriv (fun y => Q (y, r)) x) (Ioo alpha t) := by
      have hmap : MapsTo (fun r : ℝ => (x, r)) (Ioo alpha t) (univ ×ˢ Ioo alpha s) :=
        fun r hr => ⟨mem_univ _, hr.1, hr.2.trans hts⟩
      apply (hQx.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        hmap).congr
      intro r hr
      exact (hdiff r ⟨hr.1, hr.2.trans hts⟩ x).deriv
    have hpow : IntervalIntegrable (fun r : ℝ =>
        (r - alpha) ^ (-(1 / 2 : ℝ))) volume alpha t := by
      simpa only [zero_add, sub_add_cancel] using
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - alpha)
          (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_right alpha
    have hB : IntervalIntegrable B volume alpha t :=
      intervalIntegrable_const.add (hpow.const_mul _)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
    apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).mp hB).mono'
      (hcont.aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with r hr
    have hrT : r ∈ Ioo alpha T := ⟨hr.1, hr.2.trans ht.2⟩
    have hrs : r ∈ Ioo alpha s := ⟨hr.1, hr.2.trans hts⟩
    have hk : m62Curvature F c r x ≤ Real.sqrt R := by
      nlinarith only [curvature_sq F c r x, hcurv r hrT x,
        Real.sq_sqrt hR, Real.sqrt_nonneg R]
    have hu : 0 ≤ J / Real.sqrt (r - alpha) := div_nonneg hJ (Real.sqrt_nonneg _)
    have hco : K + 2 * K * m62Curvature F c r x +
        2 * m62Curvature F c r x *
          (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) ≤
        K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (r - alpha)) := by
      exact add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hk (by positivity)))
        ((mul_le_mul_of_nonneg_left (hshort r hrT x)
          (mul_nonneg (by norm_num) (curvature_nonneg F c r x))).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hu))
    have hco0 : 0 ≤ K + 2 * K * Real.sqrt R +
        2 * Real.sqrt R * (J / Real.sqrt (r - alpha)) := by positivity
    have hp : (r - alpha) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (r - alpha))⁻¹ := by
      rw [Real.rpow_neg (sub_nonneg.mpr hr.1.le), ← Real.sqrt_eq_rpow]
    have hb := normalizationCoefficient_spatial_abs_bound (Fs s hs) c (hcs s hs)
      (hBs s hs) hrs x
    rw [hjetEq s hs] at hb
    rw [Real.norm_eq_abs]
    calc
      _ ≤ curveSpeed F c r x * (K + 2 * K * m62Curvature F c r x +
          2 * m62Curvature F c r x *
            (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x)) := hb
      _ ≤ curveSpeed F c r x *
          (K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (r - alpha))) :=
        mul_le_mul_of_nonneg_left hco (speed_nonneg F c r x)
      _ ≤ V * (K + 2 * K * Real.sqrt R +
          2 * Real.sqrt R * (J / Real.sqrt (r - alpha))) :=
        mul_le_mul_of_nonneg_right (hspeed r (Ioo_subset_Ico_self hrT) x).2 hco0
      _ = B r := by dsimp only [B]; rw [hp]; ring

end PoincareConjecture.M63
