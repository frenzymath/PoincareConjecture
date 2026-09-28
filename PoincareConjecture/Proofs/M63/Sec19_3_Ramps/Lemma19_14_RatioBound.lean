import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Lemma19_14_RatioEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63SmoothRampRatio_bound
    {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M62CurveEstimates P.flow c K0 K1 K2) {m R0 : ℝ} (hm : 0 < m)
    (hinit : ∀ x, m ≤ m62Slope P c a x)
    (hR : ∀ x, m63RampRatio P c 1 a x ≤ R0) :
    ∀ t ∈ Icc a b, ∀ x,
      m63RampRatio P c 1 t x ≤
        (R0 + m62C1 K0 K1 K2 * Real.exp (K2 * (b - a)) / m * (t - a)) *
          Real.exp ((m62C1 K0 K1 K2 + K2) * (t - a)) := by
  let := P.charts.chartedSpace
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    exact hne (by linarith [hs.1, hs.2, ht.1, ht.2])
  have hC : 0 ≤ m62C1 K0 K1 K2 := by
    dsimp only [m62C1, m62C0]
    positivity
  have hlower := m63SmoothSlope_lower P c hc hBounds hm.le hinit
  have hu : ∀ t ∈ Icc a b, ∀ x, 0 < m62Slope P c t x :=
    fun t ht x => (mul_pos hm (Real.exp_pos _)).trans_le (hlower t ht x)
  have hforcing (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      m62C1 K0 K1 K2 / m62Slope P c t x ≤
        m62C1 K0 K1 K2 * Real.exp (K2 * (b - a)) / m := by
    have hmin : m * Real.exp (-K2 * (b - a)) ≤ m62Slope P c t x := by
      apply le_trans _ (hlower t ht x)
      apply mul_le_mul_of_nonneg_left _ hm.le
      exact Real.exp_le_exp.mpr (by nlinarith only [ht.2, h2])
    calc
      _ ≤ m62C1 K0 K1 K2 / (m * Real.exp (-K2 * (b - a))) :=
        div_le_div_of_nonneg_left hC (mul_pos hm (Real.exp_pos _)) hmin
      _ = _ := by
        rw [show -K2 * (b - a) = -(K2 * (b - a)) by ring, Real.exp_neg]
        field_simp
  have hw (t : ℝ) (ht : t ∈ Ioo a b) :
      ContDiff ℝ ∞ (fun x => (curveSpeed P.flow c t x)⁻¹) :=
    ((M62.speed_joint_contDiffOn P.flow c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)).inv
        (fun x => (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x).ne')
  have hq (t : ℝ) (ht : t ∈ Ioo a b) : ContDiff ℝ ∞ (m63RampRatio P c 1 t) :=
    (m63RampRatio_contDiffOn P c hc hu (by norm_num : (0 : ℝ) < 1)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have h := Poincare.Parabolic.periodic_le_affine_mul_exp_of_weighted_parabolic_le
    (F := fun x t => m63RampRatio P c 1 t x)
    (V := fun x t => deriv (fun s => m63RampRatio P c 1 s x) t)
    (w := fun x t => (curveSpeed P.flow c t x)⁻¹)
    (B := fun x t => 2 * m62ArcDerivative P.flow c t (m62Slope P c t) x /
      m62Slope P c t x) (p := curvePeriod) (K := m62C1 K0 K1 K2 + K2)
    (d := m62C1 K0 K1 K2 * Real.exp (K2 * (b - a)) / m) (R := R0)
    (by unfold curvePeriod; positivity) hab (add_nonneg hC h2)
    (div_nonneg (mul_nonneg hC (Real.exp_pos _).le) hm.le)
    (m63RampRatio_continuousOn P c hc hu 1)
    (fun t ht => m63RampRatio_periodic P c hc 1 ht)
    (fun x t ht => (m63RampRatio_differentiableAt_time P c hc hu (by norm_num) ht x).hasDerivAt)
    (fun x t ht => (hw t ht).differentiable (by simp) x)
    (fun x t ht => (contDiff_infty_iff_deriv.mp (hq t ht)).2.differentiable (by simp) x)
    (fun x t ht => (m63SmoothRampRatio_evolution P c hc hBounds hE hu (by norm_num) ht x).trans
      (add_le_add le_rfl (hforcing t (Ioo_subset_Icc_self ht) x))) hR
  exact fun t ht x => h x t ht

theorem m63SmoothRampCurvature_bound
    {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (h0 : 0 ≤ K0) (h1 : 0 ≤ K1) (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M62CurveEstimates P.flow c K0 K1 K2) {m R0 : ℝ} (hm : 0 < m)
    (hinit : ∀ x, m ≤ m62Slope P c a x)
    (hR : ∀ x, m63RampRatio P c 1 a x ≤ R0) :
    ∀ t ∈ Icc a b, ∀ x,
      m62Curvature P.flow c t x ≤
        (R0 + m62C1 K0 K1 K2 * Real.exp (K2 * (b - a)) / m * (t - a)) *
          Real.exp ((m62C1 K0 K1 K2 + K2) * (t - a)) := by
  intro t ht x
  have hu : 0 < m62Slope P c t x := (mul_pos hm (Real.exp_pos _)).trans_le
    (m63SmoothSlope_lower P c hc hBounds hm.le hinit t ht x)
  have hu1 := (abs_le.mp ((M62.slope_laws P c hc hBounds).abs_le_one t ht x)).2
  calc
    _ ≤ m62RegularizedCurvature P.flow c 1 t x := M62.curvature_le_regularized P.flow c 1 t x
    _ ≤ m63RampRatio P c 1 t x :=
      le_div_self (M62.regularized_pos P.flow c (by norm_num : (0 : ℝ) < 1) t x).le hu hu1
    _ ≤ _ := m63SmoothRampRatio_bound P c hc h0 h1 h2 hBounds hE hm hinit hR t ht x

end PoincareConjecture
