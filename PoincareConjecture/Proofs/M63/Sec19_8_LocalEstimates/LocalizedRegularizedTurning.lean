import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.RegularizedCutoffDensity
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ArcCutoffBoundary
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ArcCutoffIntegral
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ArcGreenIdentity

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)

theorem m63ArcCutoff_regularizedIntegral_deriv_le (hc : M62ShrinkingCurve F c)
    {K0 K1 K2 : ℝ} (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {alpha beta x0 : ℝ} (hab : alpha ≤ beta) (hx0 : x0 ∈ Icc alpha beta)
    {t ε r B P1 P2 : ℝ} (ht : t ∈ Ioo a b) (hε : 0 < ε) (hr : 0 < r)
    (hB : 0 ≤ B) (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2)
    (hcap : ∀ x ∈ Icc alpha beta, m62Curvature F c t x ≤ B)
    (psi : ℝ → ℝ) (hpsi : ContDiff ℝ 2 psi)
    (hpsiRange : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
    (hSupport : tsupport psi ⊆ Ioo (-(9 / 20 : ℝ)) (9 / 20 : ℝ))
    (hpsi1 : ∀ z, |deriv psi z| ≤ P1)
    (hpsi2 : ∀ z, |deriv (deriv psi) z| ≤ P2)
    (hLeft : (9 / 20 : ℝ) * r ≤ m63ArcLength F c t alpha x0)
    (hRight : (9 / 20 : ℝ) * r ≤ m63ArcLength F c t x0 beta) :
    let I : ℝ → ℝ := fun tau => ∫ x in alpha..beta,
      psi (m63ArcLength F c tau x0 x / r) *
        m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x
    DifferentiableAt ℝ I t ∧ deriv I t ≤
      (P2 / r ^ 2 + (P1 / r) * (K2 * m63ArcLength F c t alpha beta +
        B * m63ArcTotalCurvature F c t alpha beta)) *
          (m63ArcTotalCurvature F c t alpha beta + ε * m63ArcLength F c t alpha beta) +
        (m62C1 K0 K1 K2 + K2) * I t + m62C1 K0 K1 K2 * m63ArcLength F c t alpha beta := by
  dsimp only
  let phi := fun x => psi (m63ArcLength F c t x0 x / r)
  let h := m62RegularizedCurvature F c ε t
  let v := curveSpeed F c t
  let I : ℝ → ℝ := fun tau => ∫ x in alpha..beta,
    psi (m63ArcLength F c tau x0 x / r) *
      m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x
  let Zt := fun x => deriv (fun tau => psi (m63ArcLength F c tau x0 x / r) *
    m62RegularizedCurvature F c ε tau x * curveSpeed F c tau x) t
  let L := m63ArcLength F c t alpha beta
  let Theta := m63ArcTotalCurvature F c t alpha beta
  let C1 := m62C1 K0 K1 K2
  let A := C1 + K2
  let C := (P1 / r) * (K2 * L + B * Theta)
  let J := ∫ x in alpha..beta, h x * v x
  let G := ∫ x in alpha..beta, phi x * m62ArcSecondDerivative F c t h x * v x
  let Lphi := ∫ x in alpha..beta, phi x * v x
  change DifferentiableAt ℝ I t ∧ deriv I t ≤
    (P2 / r ^ 2 + C) * (Theta + ε * L) + A * I t + C1 * L
  have hclosed := Ioo_subset_Icc_self ht
  obtain ⟨_hIc, hZtc, _hZtime, hItime⟩ :=
    m63ArcCutoff_regularizedIntegral_time_regular F c hc alpha beta x0 r hε psi hpsi
  have hIt : HasDerivAt I (∫ x in alpha..beta, Zt x) t := hItime t ht
  refine ⟨hIt.differentiableAt, ?_⟩
  have hZt : Continuous Zt := hZtc.comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hv : ContDiff ℝ ∞ v := (speed_joint_contDiffOn F c hc).comp_contDiff
    (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hh : ContDiff ℝ 2 h :=
    ((regularized_smooth F c hε (curvatureSquared_contDiffOn F c hc)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hphi : ContDiff ℝ 2 phi := m63ArcCutoff_contDiff_two F c hc hclosed x0 r psi hpsi
  have hvpos (x : ℝ) : 0 < v x := speed_pos F c hc hclosed x
  have hh0 (x : ℝ) : 0 ≤ h x := (regularized_pos F c hε t x).le
  have hphi0 (x : ℝ) : 0 ≤ phi x := (hpsiRange _).1
  have hfirst {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
      ContDiff ℝ 1 (m62ArcDerivative F c t f) :=
    ((hv.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).inv (fun x => (hvpos x).ne')).mul hf.deriv'
  have hsecond {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
      Continuous (m62ArcSecondDerivative F c t f) :=
    (hv.continuous.inv₀ (fun x => (hvpos x).ne')).mul (hfirst hf).continuous_deriv_one
  have hJi : IntervalIntegrable (fun x => h x * v x) volume alpha beta :=
    (hh.continuous.mul hv.continuous).intervalIntegrable alpha beta
  have hGi : IntervalIntegrable
      (fun x => phi x * m62ArcSecondDerivative F c t h x * v x) volume alpha beta :=
    ((hphi.continuous.mul (hsecond hh)).mul hv.continuous).intervalIntegrable alpha beta
  have hIi : IntervalIntegrable (fun x => phi x * h x * v x) volume alpha beta :=
    ((hphi.continuous.mul hh.continuous).mul hv.continuous).intervalIntegrable alpha beta
  have hLi : IntervalIntegrable (fun x => phi x * v x) volume alpha beta :=
    (hphi.continuous.mul hv.continuous).intervalIntegrable alpha beta
  have hpoint (x : ℝ) (hx : x ∈ Icc alpha beta) :
      Zt x ≤ C * (h x * v x) + phi x * m62ArcSecondDerivative F c t h x * v x +
        A * (phi x * h x * v x) + C1 * (phi x * v x) := by
    have hp := (m63ArcCutoff_regularizedDensity_deriv_le F c hc h0 h1 h2 hBounds
      hab hx0 hx ht hε hr hB hcap psi hP1 hpsi (hpsiRange _).1 (hpsi1 _)).2
    calc
      _ ≤ (C * h x + phi x * m62ArcSecondDerivative F c t h x +
          A * phi x * h x + C1 * phi x) * v x := hp
      _ = _ := by ring
  have hstart : deriv I t ≤ C * J + G + A * I t + C1 * Lphi := by
    rw [hIt.deriv]
    calc
      _ ≤ ∫ x in alpha..beta,
          C * (h x * v x) + phi x * m62ArcSecondDerivative F c t h x * v x +
            A * (phi x * h x * v x) + C1 * (phi x * v x) :=
        intervalIntegral.integral_mono_on hab (hZt.intervalIntegrable alpha beta)
          ((((hJi.const_mul C).add hGi).add (hIi.const_mul A)).add (hLi.const_mul C1)) hpoint
      _ = _ := by
        rw [intervalIntegral.integral_add (((hJi.const_mul C).add hGi).add (hIi.const_mul A))
            (hLi.const_mul C1),
          intervalIntegral.integral_add ((hJi.const_mul C).add hGi) (hIi.const_mul A),
          intervalIntegral.integral_add (hJi.const_mul C) hGi,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  obtain ⟨hphiA, hphiB, hDA, hDB⟩ :=
    m63ArcCutoff_boundary_zero F c hc hclosed hr alpha beta x0 psi hpsi hSupport hLeft hRight
  have htransfer : G = ∫ x in alpha..beta,
      h x * m62ArcSecondDerivative F c t phi x * v x :=
    m63ArcSecond_integral_transfer F c hc ht phi h hphi hh alpha beta hphiA hphiB hDA hDB
  have hgreen : G ≤ (P2 / r ^ 2) * J := by
    rw [htransfer]
    calc
      _ ≤ ∫ x in alpha..beta, (P2 / r ^ 2) * (h x * v x) := by
        apply intervalIntegral.integral_mono_on hab
          (((hh.continuous.mul (hsecond hphi)).mul hv.continuous).intervalIntegrable alpha beta)
          (hJi.const_mul (P2 / r ^ 2))
        intro x _hx
        have hcut : m62ArcSecondDerivative F c t phi x ≤ P2 / r ^ 2 :=
          (le_abs_self _).trans (m63ArcCutoff_spatial_abs_bounds F c hc hclosed hr x0 x
            psi hpsi (hpsi1 _) (hpsi2 _)).2
        calc
          _ ≤ h x * (P2 / r ^ 2) * v x := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcut (hh0 x)) (hvpos x).le
          _ = _ := by ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hLphi : Lphi ≤ L := by
    apply intervalIntegral.integral_mono_on hab hLi (hv.continuous.intervalIntegrable alpha beta)
    intro x _hx
    exact mul_le_of_le_one_left (hvpos x).le (hpsiRange _).2
  have hk : Continuous (m62Curvature F c t) :=
    (curvature_continuousOn F c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, hclosed⟩)
  have hJ : J ≤ Theta + ε * L := by
    calc
      _ ≤ ∫ x in alpha..beta, (m62Curvature F c t x + ε) * v x := by
        apply intervalIntegral.integral_mono_on hab hJi
          (((hk.add continuous_const).mul hv.continuous).intervalIntegrable alpha beta)
        intro x _hx
        change h x * v x ≤ (m62Curvature F c t x + ε) * v x
        have herr : h x - m62Curvature F c t x ≤ ε :=
          regularized_sub_curvature_le F c hε.le t x
        exact mul_le_mul_of_nonneg_right
          (by linarith only [herr]) (hvpos x).le
      _ = Theta + ε * L := by
        have hki : IntervalIntegrable (fun x => m62Curvature F c t x * v x)
            volume alpha beta := (hk.mul hv.continuous).intervalIntegrable alpha beta
        have hvi : IntervalIntegrable (fun x => ε * v x) volume alpha beta :=
          (hv.continuous.const_mul ε).intervalIntegrable alpha beta
        simp_rw [add_mul]
        rw [intervalIntegral.integral_add hki hvi, intervalIntegral.integral_const_mul]
        rfl
  have hL : 0 ≤ L := intervalIntegral.integral_nonneg_of_forall hab (speed_nonneg F c t)
  have hTheta : 0 ≤ Theta := intervalIntegral.integral_nonneg_of_forall hab
    (fun x => mul_nonneg (curvature_nonneg F c t x) (speed_nonneg F c t x))
  have hC1 : 0 ≤ C1 := by
    dsimp only [C1, m62C1, m62C0]
    positivity
  have hcoef : 0 ≤ P2 / r ^ 2 + C := add_nonneg (div_nonneg hP2 (sq_nonneg r))
    (mul_nonneg (div_nonneg hP1 hr.le)
      (add_nonneg (mul_nonneg h2 hL) (mul_nonneg hB hTheta)))
  calc
    deriv I t ≤ C * J + G + A * I t + C1 * Lphi := hstart
    _ ≤ C * J + (P2 / r ^ 2) * J + A * I t + C1 * L := by
      linarith [mul_le_mul_of_nonneg_left hLphi hC1]
    _ = (P2 / r ^ 2 + C) * J + A * I t + C1 * L := by ring
    _ ≤ (P2 / r ^ 2 + C) * (Theta + ε * L) + A * I t + C1 * L := by
      linarith only [mul_le_mul_of_nonneg_left hJ hcoef]

end PoincareConjecture
