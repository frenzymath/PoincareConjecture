import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2RatioRegularity
import PoincareConjecture.Proofs.M63.Mathlib.WeightedDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem c2_rampRatio_evolution (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) (hT : a < T) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M63C2CurveEstimates P.flow c T K0 K1 K2)
    (hu : ∀ t ∈ Icc a T, ∀ x, 0 < m62Slope P c t x)
    {epsilon t : ℝ} (hepsilon : 0 < epsilon) (ht : t ∈ Ioo a T) (x : ℝ) :
    deriv (fun s => m63RampRatio P c epsilon s x) t ≤
      m62ArcSecondDerivative P.flow c t (m63RampRatio P c epsilon t) x +
        2 * m62ArcDerivative P.flow c t (m62Slope P c t) x / m62Slope P c t x *
          m62ArcDerivative P.flow c t (m63RampRatio P c epsilon t) x +
        (m62C1 K0 K1 K2 + K2) * m63RampRatio P c epsilon t x +
        m62C1 K0 K1 K2 / m62Slope P c t x := by
  let := P.charts.chartedSpace
  have ht' := Ioo_subset_Icc_self ht
  have hup (y : ℝ) := hu t ht' y
  have hreg := c2_scalar_contDiff_of_local P.flow c hc hlocal ht
  have hh := hreg.2.2 epsilon hepsilon
  have hs := c2_slope_contDiff_of_local P hlocal c hc ht
  have hw : ContDiff ℝ 1 (fun y => (curveSpeed P.flow c t y)⁻¹) :=
    hreg.1.inv (fun y => (c2_speed_pos P.flow c hc ht' y).ne')
  have hquot :
      m62ArcSecondDerivative P.flow c t (m62RegularizedCurvature P.flow c epsilon t) x /
          m62Slope P c t x -
        m62RegularizedCurvature P.flow c epsilon t x *
          m62ArcSecondDerivative P.flow c t (m62Slope P c t) x / (m62Slope P c t x) ^ 2 =
      m62ArcSecondDerivative P.flow c t (m63RampRatio P c epsilon t) x +
        2 * m62ArcDerivative P.flow c t (m62Slope P c t) x / m62Slope P c t x *
          m62ArcDerivative P.flow c t (m63RampRatio P c epsilon t) x :=
    Poincare.Parabolic.weighted_second_div hh hs (fun y => (hup y).ne')
      (hw.differentiable (by norm_num) x)
  have hht := hE.regularized_time epsilon hepsilon t ht x
  have hut := (c2_slope_laws_of_local P hlocal hBounds c hc hT).evolution t ht x
  have hS := (c2_unitTangent_norm P.flow c hc ht' x).le
  have hRic := (abs_le.mp
    (hBounds.ricci t (hc.domain_subset ht') (c x t) _ _ hS hS)).1
  change -K2 ≤ m62TangentRicci P.flow c t x at hRic
  have hqpos : 0 < m63RampRatio P c epsilon t x :=
    div_pos (M62.regularized_pos P.flow c hepsilon t x) (hup x)
  have hreaction := mul_le_mul_of_nonneg_right (neg_le_neg hRic) hqpos.le
  have hcubic : (m62Curvature P.flow c t x ^ 3 -
      m62RegularizedCurvature P.flow c epsilon t x * m62Curvature P.flow c t x ^ 2) /
        m62Slope P c t x ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (hup x).le
    nlinarith only [mul_le_mul_of_nonneg_right
      (M62.curvature_le_regularized P.flow c epsilon t x)
      (sq_nonneg (m62Curvature P.flow c t x))]
  calc
    deriv (fun s => m63RampRatio P c epsilon s x) t =
        deriv (fun s => m62RegularizedCurvature P.flow c epsilon s x) t / m62Slope P c t x -
          m62RegularizedCurvature P.flow c epsilon t x * deriv (fun s => m62Slope P c s x) t /
            (m62Slope P c t x) ^ 2 := by
      change deriv (fun s => m62RegularizedCurvature P.flow c epsilon s x / m62Slope P c s x)
        t = _
      rw [deriv_fun_div hht hut.differentiableAt (hup x).ne']
      field_simp
    _ ≤ (m62ArcSecondDerivative P.flow c t (m62RegularizedCurvature P.flow c epsilon t) x +
          m62Curvature P.flow c t x ^ 3 +
          m62C1 K0 K1 K2 * (m62RegularizedCurvature P.flow c epsilon t x + 1)) /
            m62Slope P c t x -
          m62RegularizedCurvature P.flow c epsilon t x * deriv (fun s => m62Slope P c s x) t /
            (m62Slope P c t x) ^ 2 :=
      sub_le_sub_right (div_le_div_of_nonneg_right
        (hE.regularized_bound epsilon hepsilon t ht x) (hup x).le) _
    _ = (m62ArcSecondDerivative P.flow c t (m62RegularizedCurvature P.flow c epsilon t) x /
          m62Slope P c t x -
          m62RegularizedCurvature P.flow c epsilon t x *
            m62ArcSecondDerivative P.flow c t (m62Slope P c t) x / (m62Slope P c t x) ^ 2) +
        (m62Curvature P.flow c t x ^ 3 -
          m62RegularizedCurvature P.flow c epsilon t x * m62Curvature P.flow c t x ^ 2) /
            m62Slope P c t x -
          m62TangentRicci P.flow c t x * m63RampRatio P c epsilon t x +
          m62C1 K0 K1 K2 * m63RampRatio P c epsilon t x +
            m62C1 K0 K1 K2 / m62Slope P c t x := by
      rw [hut.deriv, ← M62.curvature_sq P.flow c t x]
      dsimp only [m63RampRatio]
      field_simp [(hup x).ne']
      ring
    _ ≤ _ := by rw [hquot]; linarith only [hcubic, hreaction]

end PoincareConjecture.M63
