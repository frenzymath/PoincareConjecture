import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2RatioEvolution










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem c2_rampRatio_bound (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) (hT : a < T) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M63C2CurveEstimates P.flow c T K0 K1 K2) {m R0 : ℝ} (hm : 0 < m)
    (hinit : ∀ x, m ≤ m62Slope P c a x)
    (hR : ∀ x, m63RampRatio P c 1 a x ≤ R0) :
    ∀ t ∈ Icc a T, ∀ x,
      m63RampRatio P c 1 t x ≤
        (R0 + m62C1 K0 K1 K2 * Real.exp (K2 * (T - a)) / m * (t - a)) *
          Real.exp ((m62C1 K0 K1 K2 + K2) * (t - a)) := by
  let := P.charts.chartedSpace
  have hC : 0 ≤ m62C1 K0 K1 K2 := by
    dsimp only [m62C1, m62C0]
    positivity
  have hlower := c2_slope_lower P hlocal c hc hT hBounds hm.le hinit
  have hu : ∀ t ∈ Icc a T, ∀ x, 0 < m62Slope P c t x :=
    fun t ht x => (mul_pos hm (Real.exp_pos _)).trans_le (hlower t ht x)
  have hS := c2_slope_laws_of_local P hlocal hBounds c hc hT
  have hforcing (t : ℝ) (ht : t ∈ Icc a T) (x : ℝ) :
      m62C1 K0 K1 K2 / m62Slope P c t x ≤
        m62C1 K0 K1 K2 * Real.exp (K2 * (T - a)) / m := by
    have hmin : m * Real.exp (-K2 * (T - a)) ≤ m62Slope P c t x := by
      apply le_trans _ (hlower t ht x)
      apply mul_le_mul_of_nonneg_left _ hm.le
      exact Real.exp_le_exp.mpr (by nlinarith only [ht.2, h2])
    calc
      _ ≤ m62C1 K0 K1 K2 / (m * Real.exp (-K2 * (T - a))) :=
        div_le_div_of_nonneg_left hC (mul_pos hm (Real.exp_pos _)) hmin
      _ = _ := by
        rw [show -K2 * (T - a) = -(K2 * (T - a)) by ring, Real.exp_neg]
        field_simp
  have hw (t : ℝ) (ht : t ∈ Ioo a T) :
      ContDiff ℝ 1 (fun x => (curveSpeed P.flow c t x)⁻¹) :=
    ((c2_scalar_contDiff_of_local P.flow c hc hlocal ht).1).inv
      (fun x => (c2_speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x).ne')
  have hq' (t : ℝ) (ht : t ∈ Ioo a T) : ContDiff ℝ 1 (deriv (m63RampRatio P c 1 t)) :=
    (c2_rampRatio_contDiff P hlocal c hc (by norm_num : (0 : ℝ) < 1) ht
      (fun x => (hu t (Ioo_subset_Icc_self ht) x).ne')).deriv'
  have h := Poincare.Parabolic.periodic_le_affine_mul_exp_of_weighted_parabolic_le
    (F := fun x t => m63RampRatio P c 1 t x)
    (V := fun x t => deriv (fun s => m63RampRatio P c 1 s x) t)
    (w := fun x t => (curveSpeed P.flow c t x)⁻¹)
    (B := fun x t => 2 * m62ArcDerivative P.flow c t (m62Slope P c t) x /
      m62Slope P c t x) (p := curvePeriod) (K := m62C1 K0 K1 K2 + K2)
    (d := m62C1 K0 K1 K2 * Real.exp (K2 * (T - a)) / m) (R := R0)
    (by unfold curvePeriod; positivity) hT (add_nonneg hC h2)
    (div_nonneg (mul_nonneg hC (Real.exp_pos _).le) hm.le)
    (c2_rampRatio_continuousOn P c hc hT hu 1)
    (fun t ht => c2_rampRatio_periodic P hlocal c hc hT 1 ht)
    (fun x t ht => (c2_rampRatio_differentiableAt_time P c hE hS (by norm_num)
      ht x (hu t (Ioo_subset_Icc_self ht) x).ne').hasDerivAt)
    (fun x t ht => (hw t ht).differentiable (by norm_num) x)
    (fun x t ht => (hq' t ht).differentiable (by norm_num) x)
    (fun x t ht => (c2_rampRatio_evolution P hlocal c hc hT hBounds hE hu
      (by norm_num) ht x).trans
        (add_le_add le_rfl (hforcing t (Ioo_subset_Icc_self ht) x))) hR
  exact fun t ht x => h x t ht



theorem c2_rampCurvature_bound (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) (hT : a < T) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M63C2CurveEstimates P.flow c T K0 K1 K2) {m R0 : ℝ} (hm : 0 < m)
    (hinit : ∀ x, m ≤ m62Slope P c a x)
    (hR : ∀ x, m63RampRatio P c 1 a x ≤ R0) :
    ∀ t ∈ Icc a T, ∀ x,
      m62Curvature P.flow c t x ≤
        (R0 + m62C1 K0 K1 K2 * Real.exp (K2 * (T - a)) / m * (t - a)) *
          Real.exp ((m62C1 K0 K1 K2 + K2) * (t - a)) := by
  intro t ht x
  have hu : 0 < m62Slope P c t x := (mul_pos hm (Real.exp_pos _)).trans_le
    (c2_slope_lower P hlocal c hc hT hBounds hm.le hinit t ht x)
  have hu1 := (abs_le.mp (c2_abs_slope_le_one P c hc ht x)).2
  calc
    _ ≤ m62RegularizedCurvature P.flow c 1 t x := M62.curvature_le_regularized P.flow c 1 t x
    _ ≤ m63RampRatio P c 1 t x :=
      le_div_self (M62.regularized_pos P.flow c (by norm_num : (0 : ℝ) < 1) t x).le hu hu1
    _ ≤ _ := c2_rampRatio_bound P hlocal c hc hT h0 h1 h2 hBounds hE hm hinit hR t ht x

end PoincareConjecture.M63
