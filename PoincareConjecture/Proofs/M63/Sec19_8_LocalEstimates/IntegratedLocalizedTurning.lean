import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.LocalizedRegularizedTurning
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ArcCutoffRegularization

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)

theorem m63ArcCutoff_turning_increase_le (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {alpha beta x0 : ℝ} (hab : alpha ≤ beta) (hx0 : x0 ∈ Icc alpha beta)
    {r P1 P2 : ℝ} (hr : 0 < r) (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi)
    (hpsiRange : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
    (hSupport : tsupport psi ⊆ Ioo (-(9 / 20 : ℝ)) (9 / 20 : ℝ))
    (hpsi1 : ∀ z, |deriv psi z| ≤ P1)
    (hpsi2 : ∀ z, |deriv (deriv psi) z| ≤ P2)
    {s T Lmax Thetamax : ℝ} (hs : a ≤ s) (hT : T ≤ b) (hsT : s < T)
    (hLmax : 0 ≤ Lmax) (hThetamax : 0 ≤ Thetamax)
    (hL : ∀ tau ∈ Ioo s T, m63ArcLength F c tau alpha beta ≤ Lmax)
    (hTurning : ∀ tau ∈ Ioo s T,
      m63ArcTotalCurvature F c tau alpha beta ≤ Thetamax)
    (hCurv : ∀ tau ∈ Ioo s T, ∀ x ∈ Icc alpha beta,
      m62CurvatureSquared F c tau x ≤ 2 / (tau - s))
    (hLeft : ∀ tau ∈ Ioo s T, (9 / 20 : ℝ) * r ≤ m63ArcLength F c tau alpha x0)
    (hRight : ∀ tau ∈ Ioo s T, (9 / 20 : ℝ) * r ≤ m63ArcLength F c tau x0 beta)
    {t : ℝ} (ht : t ∈ Icc s T) :
    let I : ℝ → ℝ := fun tau => ∫ x in alpha..beta,
      psi (m63ArcLength F c tau x0 x / r) *
        m62Curvature F c tau x * curveSpeed F c tau x
    let C1 := m62C1 K0 K1 K2
    let A := C1 + K2
    let D0 := (P2 / r ^ 2 + (P1 / r) * K2 * Lmax + A) * Thetamax + C1 * Lmax
    let D1 := (P1 / r) * Real.sqrt 2 * Thetamax ^ 2
    I t ≤ I s + D0 * (t - s) + 2 * D1 * Real.sqrt (t - s) := by
  let I : ℝ → ℝ := fun tau => ∫ x in alpha..beta,
    psi (m63ArcLength F c tau x0 x / r) *
      m62Curvature F c tau x * curveSpeed F c tau x
  let Iε : ℝ → ℝ → ℝ := fun ε tau => ∫ x in alpha..beta,
    psi (m63ArcLength F c tau x0 x / r) *
      m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x
  let L : ℝ → ℝ := fun tau => m63ArcLength F c tau alpha beta
  let Theta : ℝ → ℝ := fun tau => m63ArcTotalCurvature F c tau alpha beta
  let C1 := m62C1 K0 K1 K2
  let A := C1 + K2
  let D0 := (P2 / r ^ 2 + (P1 / r) * K2 * Lmax + A) * Thetamax + C1 * Lmax
  let D1 := (P1 / r) * Real.sqrt 2 * Thetamax ^ 2
  let Heps : ℝ → ℝ := fun ε => Thetamax + ε * Lmax
  let D0eps : ℝ → ℝ := fun ε =>
    (P2 / r ^ 2 + (P1 / r) * K2 * Lmax + A) * Heps ε + C1 * Lmax
  let D1eps : ℝ → ℝ := fun ε => (P1 / r) * Real.sqrt 2 * Thetamax * Heps ε
  change I t ≤ I s + D0 * (t - s) + 2 * D1 * Real.sqrt (t - s)
  have hclosed (tau : ℝ) (htau : tau ∈ Icc s T) : tau ∈ Icc a b :=
    ⟨hs.trans htau.1, htau.2.trans hT⟩
  have hinner (tau : ℝ) (htau : tau ∈ Ioo s T) : tau ∈ Ioo a b :=
    ⟨hs.trans_lt htau.1, htau.2.trans_le hT⟩
  have hC1 : 0 ≤ C1 := by dsimp only [C1, m62C1, m62C0]; positivity
  have hA : 0 ≤ A := add_nonneg hC1 h2
  have hPdiv : 0 ≤ P1 / r := div_nonneg hP1 hr.le
  have hL0 (tau : ℝ) : 0 ≤ L tau :=
    intervalIntegral.integral_nonneg_of_forall hab (speed_nonneg F c tau)
  have hTheta0 (tau : ℝ) : 0 ≤ Theta tau :=
    intervalIntegral.integral_nonneg_of_forall hab
      (fun x => mul_nonneg (curvature_nonneg F c tau x) (speed_nonneg F c tau x))
  have hIupper (tau : ℝ) (htau : tau ∈ Icc a b) : I tau ≤ Theta tau := by
    have hv : Continuous (curveSpeed F c tau) :=
      (speed_continuousOn F c hc).comp_continuous
        (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, htau⟩)
    have hk : Continuous (m62Curvature F c tau) :=
      (curvature_continuousOn F c hc).comp_continuous
        (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, htau⟩)
    have hsigma : Continuous (fun x => m63ArcLength F c tau x0 x) :=
      (m63ArcLength_joint_continuousOn F c hc x0).comp_continuous
        (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, htau⟩)
    have hphi : Continuous (fun x => psi (m63ArcLength F c tau x0 x / r)) :=
      hpsi.continuous.comp (hsigma.div_const r)
    apply intervalIntegral.integral_mono_on hab
      (((hphi.mul hk).mul hv).intervalIntegrable alpha beta)
      ((hk.mul hv).intervalIntegrable alpha beta)
    intro x _hx
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (curvature_nonneg F c tau x) (hpsiRange _).2)
      (speed_nonneg F c tau x)
  have herror (ε : ℝ) (hε : 0 ≤ ε) (tau : ℝ) (htau : tau ∈ Icc a b) :
      0 ≤ Iε ε tau - I tau ∧ Iε ε tau - I tau ≤ ε * L tau :=
    m63ArcCutoff_regularization_error F c hc hab x0 r psi hpsi.continuous hpsiRange hε htau
  have hregularized (ε : ℝ) (hε : 0 < ε) :
      Iε ε t ≤ Iε ε s + D0eps ε * (t - s) + 2 * D1eps ε * Real.sqrt (t - s) := by
    have hderiv (tau : ℝ) (htau : tau ∈ Ioo s T) :
        DifferentiableAt ℝ (Iε ε) tau ∧
          deriv (Iε ε) tau ≤ D0eps ε + D1eps ε / Real.sqrt (tau - s) := by
      let B := Real.sqrt 2 / Real.sqrt (tau - s)
      have hB : 0 ≤ B := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hcap (x : ℝ) (hx : x ∈ Icc alpha beta) : m62Curvature F c tau x ≤ B :=
        (Real.sqrt_le_sqrt (hCurv tau htau x hx)).trans_eq
          (Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2) (tau - s))
      have hraw := m63ArcCutoff_regularizedIntegral_deriv_le F c hc h0 h1 h2 hBounds
        hab hx0 (hinner tau htau) hε hr hB hP1 hP2 hcap psi hpsi hpsiRange
        hSupport hpsi1 hpsi2 (hLeft tau htau) (hRight tau htau)
      refine ⟨hraw.1, ?_⟩
      have hsum : Theta tau + ε * L tau ≤ Heps ε :=
        add_le_add (hTurning tau htau) (mul_le_mul_of_nonneg_left (hL tau htau) hε.le)
      have hsum0 : 0 ≤ Theta tau + ε * L tau :=
        add_nonneg (hTheta0 tau) (mul_nonneg hε.le (hL0 tau))
      have hIe : Iε ε tau ≤ Heps ε := by
        have herr := (herror ε hε.le tau (Ioo_subset_Icc_self (hinner tau htau))).2
        have hI := hIupper tau (Ioo_subset_Icc_self (hinner tau htau))
        linarith only [herr, hI, hsum]
      have hcoef : P2 / r ^ 2 + (P1 / r) * (K2 * L tau + B * Theta tau) ≤
          P2 / r ^ 2 + (P1 / r) * (K2 * Lmax + B * Thetamax) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left (hL tau htau) h2)
            (mul_le_mul_of_nonneg_left (hTurning tau htau) hB)) hPdiv)
      have hcoef0 : 0 ≤ P2 / r ^ 2 + (P1 / r) * (K2 * Lmax + B * Thetamax) :=
        add_nonneg (div_nonneg hP2 (sq_nonneg r))
          (mul_nonneg hPdiv (add_nonneg (mul_nonneg h2 hLmax) (mul_nonneg hB hThetamax)))
      calc
        deriv (Iε ε) tau ≤
            (P2 / r ^ 2 + (P1 / r) * (K2 * L tau + B * Theta tau)) *
              (Theta tau + ε * L tau) + A * Iε ε tau + C1 * L tau := hraw.2
        _ ≤ (P2 / r ^ 2 + (P1 / r) * (K2 * Lmax + B * Thetamax)) *
              Heps ε + A * Heps ε + C1 * Lmax := by
          exact add_le_add
            (add_le_add (mul_le_mul hcoef hsum hsum0 hcoef0)
              (mul_le_mul_of_nonneg_left hIe hA))
            (mul_le_mul_of_nonneg_left (hL tau htau) hC1)
        _ = D0eps ε + D1eps ε / Real.sqrt (tau - s) := by
          dsimp only [D0eps, D1eps, B]
          ring
    let G : ℝ → ℝ := fun tau => Iε ε tau - D0eps ε * (tau - s) -
      2 * D1eps ε * Real.sqrt (tau - s)
    have hIecont : ContinuousOn (Iε ε) (Icc s T) :=
      (m63ArcCutoff_regularizedIntegral_time_regular F c hc alpha beta x0 r hε psi hpsi).1.mono
        (Icc_subset_Icc hs hT)
    have hGc : ContinuousOn G (Icc s T) :=
      (hIecont.sub (by fun_prop)).sub (by fun_prop)
    have hGd (tau : ℝ) (htau : tau ∈ Ioo s T) :
        HasDerivAt G
          (deriv (Iε ε) tau - D0eps ε - D1eps ε / Real.sqrt (tau - s)) tau := by
      have hroot : Real.sqrt (tau - s) ≠ 0 :=
        (Real.sqrt_pos.mpr (sub_pos.mpr htau.1)).ne'
      have hlinear := ((hasDerivAt_id tau).sub_const s).const_mul (D0eps ε)
      have hsqrt := (((hasDerivAt_id tau).sub_const s).sqrt
        (sub_pos.mpr htau.1).ne').const_mul (2 * D1eps ε)
      apply (((hderiv tau htau).1.hasDerivAt.sub hlinear).sub hsqrt).congr_deriv
      simp only [id_eq]
      field_simp [hroot]
    have hmono : AntitoneOn G (Icc s T) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s T) hGc
        (fun tau htau => (hGd tau (by simpa only [interior_Icc] using htau)).hasDerivWithinAt)
        (fun tau htau => by
          have hd := (hderiv tau (by simpa only [interior_Icc] using htau)).2
          linarith only [hd])
    have h := hmono (show s ∈ Icc s T from ⟨le_rfl, hsT.le⟩) ht ht.1
    dsimp only [G] at h
    simp only [sub_self, Real.sqrt_zero, mul_zero, sub_zero] at h
    linarith only [h]
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      I t ≤ I s + ε * L s + D0eps ε * (t - s) + 2 * D1eps ε * Real.sqrt (t - s) := by
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)] with ε hε
    have hcomp := hregularized ε hε
    have herrt := (herror ε hε.le t (hclosed t ht)).1
    have herrs := (herror ε hε.le s (hclosed s ⟨le_rfl, hsT.le⟩)).2
    linarith only [hcomp, herrt, herrs]
  have hlim : Tendsto
      (fun ε : ℝ => I s + ε * L s + D0eps ε * (t - s) +
        2 * D1eps ε * Real.sqrt (t - s)) (𝓝[>] 0)
      (𝓝 (I s + D0 * (t - s) + 2 * D1 * Real.sqrt (t - s))) := by
    have hcont : Continuous (fun ε : ℝ => I s + ε * L s + D0eps ε * (t - s) +
        2 * D1eps ε * Real.sqrt (t - s)) := by
      dsimp only [D0eps, D1eps, Heps]
      fun_prop
    have hvalue : I s + (0 : ℝ) * L s + D0eps 0 * (t - s) +
        2 * D1eps 0 * Real.sqrt (t - s) =
        I s + D0 * (t - s) + 2 * D1 * Real.sqrt (t - s) := by
      dsimp only [D0eps, D1eps, Heps, D0, D1]
      ring
    rw [← hvalue]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim hevent

end PoincareConjecture
