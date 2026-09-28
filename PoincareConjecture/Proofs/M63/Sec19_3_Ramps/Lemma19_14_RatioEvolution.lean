import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RatioRegularity
import PoincareConjecture.Proofs.M63.Mathlib.WeightedDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63SmoothRampRatio_evolution
    {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hE : M62CurveEstimates P.flow c K0 K1 K2)
    (hu : ∀ t ∈ Icc a b, ∀ x, 0 < m62Slope P c t x)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Ioo a b) (x : ℝ) :
    deriv (fun s => m63RampRatio P c ε s x) t ≤
      m62ArcSecondDerivative P.flow c t (m63RampRatio P c ε t) x +
        2 * m62ArcDerivative P.flow c t (m62Slope P c t) x / m62Slope P c t x *
          m62ArcDerivative P.flow c t (m63RampRatio P c ε t) x +
        (m62C1 K0 K1 K2 + K2) * m63RampRatio P c ε t x +
        m62C1 K0 K1 K2 / m62Slope P c t x := by
  let := P.charts.chartedSpace
  have hup (y : ℝ) := hu t (Ioo_subset_Icc_self ht) y
  have hhjoint := M62.regularized_smooth P.flow c hε
    (M62.curvatureSquared_contDiffOn P.flow c hc)
  have hh : ContDiff ℝ ∞ (m62RegularizedCurvature P.flow c ε t) :=
    hhjoint.comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, ht⟩)
  have hs : ContDiff ℝ ∞ (m62Slope P c t) :=
    (m63Slope_contDiffOn P c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hw : ContDiff ℝ ∞ (fun y => (curveSpeed P.flow c t y)⁻¹) :=
    ((M62.speed_joint_contDiffOn P.flow c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)).inv
        (fun y => (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self ht) y).ne')
  have hquot :
      m62ArcSecondDerivative P.flow c t (m62RegularizedCurvature P.flow c ε t) x /
          m62Slope P c t x -
        m62RegularizedCurvature P.flow c ε t x *
          m62ArcSecondDerivative P.flow c t (m62Slope P c t) x / (m62Slope P c t x) ^ 2 =
      m62ArcSecondDerivative P.flow c t (m63RampRatio P c ε t) x +
        2 * m62ArcDerivative P.flow c t (m62Slope P c t) x / m62Slope P c t x *
          m62ArcDerivative P.flow c t (m63RampRatio P c ε t) x := by
    exact Poincare.Parabolic.weighted_second_div (hh.of_le (by decide))
      (hs.of_le (by decide)) (fun y => (hup y).ne') (hw.differentiable (by simp) x)
  have hht : DifferentiableAt ℝ (fun s => m62RegularizedCurvature P.flow c ε s x) t := by
    have h := hhjoint.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (x, t) ∈ univ ×ˢ Ioo a b from ⟨mem_univ _, ht⟩))
    exact (h.comp t (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt
      (by simp)
  have hut := M62.hasDerivAt_slope P c hc ht x
  have hS := (M62.unitTangent_norm P.flow c hc (Ioo_subset_Icc_self ht) x).le
  have hRic := (abs_le.mp (hBounds.ricci t (Ioo_subset_Icc_self ht) (c x t) _ _ hS hS)).1
  change -K2 ≤ m62TangentRicci P.flow c t x at hRic
  have hqpos : 0 < m63RampRatio P c ε t x :=
    div_pos (M62.regularized_pos P.flow c hε t x) (hup x)
  have hreaction := mul_le_mul_of_nonneg_right (neg_le_neg hRic) hqpos.le
  have hcubic : (m62Curvature P.flow c t x ^ 3 -
      m62RegularizedCurvature P.flow c ε t x * m62Curvature P.flow c t x ^ 2) /
        m62Slope P c t x ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (hup x).le
    nlinarith only [mul_le_mul_of_nonneg_right
      (M62.curvature_le_regularized P.flow c ε t x) (sq_nonneg (m62Curvature P.flow c t x))]
  calc
    deriv (fun s => m63RampRatio P c ε s x) t =
        deriv (fun s => m62RegularizedCurvature P.flow c ε s x) t / m62Slope P c t x -
          m62RegularizedCurvature P.flow c ε t x * deriv (fun s => m62Slope P c s x) t /
            (m62Slope P c t x) ^ 2 := by
      change deriv (fun s => m62RegularizedCurvature P.flow c ε s x / m62Slope P c s x) t = _
      rw [deriv_fun_div hht hut.differentiableAt (hup x).ne']
      field_simp
    _ ≤ (m62ArcSecondDerivative P.flow c t (m62RegularizedCurvature P.flow c ε t) x +
          m62Curvature P.flow c t x ^ 3 +
          m62C1 K0 K1 K2 * (m62RegularizedCurvature P.flow c ε t x + 1)) /
            m62Slope P c t x -
          m62RegularizedCurvature P.flow c ε t x * deriv (fun s => m62Slope P c s x) t /
            (m62Slope P c t x) ^ 2 :=
      sub_le_sub_right (div_le_div_of_nonneg_right (hE.regularized_bound ε hε t ht x)
        (hup x).le) _
    _ = (m62ArcSecondDerivative P.flow c t (m62RegularizedCurvature P.flow c ε t) x /
          m62Slope P c t x -
          m62RegularizedCurvature P.flow c ε t x *
            m62ArcSecondDerivative P.flow c t (m62Slope P c t) x / (m62Slope P c t x) ^ 2) +
        (m62Curvature P.flow c t x ^ 3 -
          m62RegularizedCurvature P.flow c ε t x * m62Curvature P.flow c t x ^ 2) /
            m62Slope P c t x -
          m62TangentRicci P.flow c t x * m63RampRatio P c ε t x +
          m62C1 K0 K1 K2 * m63RampRatio P c ε t x + m62C1 K0 K1 K2 / m62Slope P c t x := by
      rw [hut.deriv, ← M62.curvature_sq P.flow c t x]
      dsimp only [m63RampRatio]
      field_simp [(hup x).ne']
      ring
    _ ≤ _ := by rw [hquot]; linarith only [hcubic, hreaction]

end PoincareConjecture
