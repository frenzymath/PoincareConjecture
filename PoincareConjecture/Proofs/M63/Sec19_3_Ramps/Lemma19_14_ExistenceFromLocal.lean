import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ClosedContinuation
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RampInitialBounds
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2RatioBound












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem c2_ramp_existence_of_local (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hest : ∀ T, a < T → T ≤ b → ∀ c : ℝ → ℝ → P.charts.Point,
      M63C2ShrinkingCurveOn P.flow c (Icc a T) →
        M63C2CurveEstimates P.flow c T K0 K1 K2) : M63C2RampExistence P := by
  intro gamma hper hreg hramp
  obtain ⟨T0, hT0, hT0b, c0, hc0, hinit0, _⟩ :=
    hlocal.local_existence gamma hper hreg (ramp_immersed P hramp)
  have hramp0 : M63IsRampAt P (fun x => c0 x a) a := by
    rw [show (fun x => c0 x a) = gamma from funext hinit0]
    exact hramp
  obtain ⟨m, R0, hm, hR0, hmin, hmax⟩ :=
    c2_initial_ramp_bounds P hlocal c0 hc0 hT0 hramp0
  let C := m62C1 K0 K1 K2
  have hC : 0 ≤ C := by dsimp only [C, m62C1, m62C0]; positivity
  have hD : 0 ≤ b - a := sub_nonneg.mpr (hT0.le.trans hT0b)
  let K := (R0 + C * Real.exp (K2 * (b - a)) / m * (b - a)) *
    Real.exp ((C + K2) * (b - a))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbound (T : ℝ) (hT : a < T) (hTb : T ≤ b) (c : ℝ → ℝ → P.charts.Point)
      (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) (hinit : ∀ x, c x a = gamma x) :
      ∀ t ∈ Icc a T, ∀ x, m62Curvature P.flow c t x ≤ K := by
    have hslice : ∀ x, c x a = c0 x a := fun x => (hinit x).trans (hinit0 x).symm
    have hmin' (x : ℝ) : m ≤ m62Slope P c a x := by
      rw [slope_congr_slice P hslice]
      exact hmin x
    have hmax' (x : ℝ) : m63RampRatio P c 1 a x ≤ R0 := by
      rw [rampRatio_congr_slice P hslice]
      exact hmax x
    have hcurv := c2_rampCurvature_bound P hlocal c hc hT h0 h1 h2 hBounds
      (hest T hT hTb c hc) hm hmin' hmax'
    intro t ht x
    apply (hcurv t ht x).trans
    have htime : t - a ≤ b - a := sub_le_sub_right (ht.2.trans hTb) a
    have htime0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hcoeff : C * Real.exp (K2 * (T - a)) / m ≤
        C * Real.exp (K2 * (b - a)) / m := by
      apply div_le_div_of_nonneg_right _ hm.le
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_sub_right hTb a) h2)
    have hsum : R0 + C * Real.exp (K2 * (T - a)) / m * (t - a) ≤
        R0 + C * Real.exp (K2 * (b - a)) / m * (b - a) :=
      add_le_add le_rfl (mul_le_mul hcoeff htime htime0 (by positivity))
    have hexp : Real.exp ((C + K2) * (t - a)) ≤ Real.exp ((C + K2) * (b - a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime (add_nonneg hC h2))
    exact mul_le_mul hsum hexp (Real.exp_pos _).le (by positivity)
  obtain ⟨c, hc, hinit, hintrinsic⟩ :=
    c2_exists_closed_of_uniform_curvature hlocal gamma hper hreg
      (ramp_immersed P hramp) K hK hbound
  refine ⟨c, hc, hinit, hintrinsic, ?_⟩
  apply c2_ramp_preserved P hlocal c hc (hT0.trans_le hT0b) hBounds
  rw [show (fun x => c x a) = gamma from funext hinit]
  exact hramp




theorem smooth_ramp_existence_of_local (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hest : ∀ T, a < T → T ≤ b → ∀ c : ℝ → ℝ → P.charts.Point,
      M63C2ShrinkingCurveOn P.flow c (Icc a T) →
        M63C2CurveEstimates P.flow c T K0 K1 K2) : M63SmoothRampExistence P := by
  intro gamma hper hreg hramp
  obtain ⟨c, hc, hinit, hintrinsic, hramps⟩ :=
    c2_ramp_existence_of_local P hlocal h0 h1 h2 hBounds hest gamma hper
      (hreg.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) hramp
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith [hs.1, hs.2, ht.1, ht.2]
  have hinitial : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ (fun x => c x a) := by
    rw [show (fun x => c x a) = gamma from funext hinit]
    exact hreg
  have hsmooth := hlocal.smooth_initial_upgrade b hab le_rfl (Icc a b)
    (Or.inl rfl) c hc hinitial
  exact ⟨c, m63SmoothClosed_iff_m62.mp hsmooth, hinit, hintrinsic, hramps⟩

end PoincareConjecture.M63
