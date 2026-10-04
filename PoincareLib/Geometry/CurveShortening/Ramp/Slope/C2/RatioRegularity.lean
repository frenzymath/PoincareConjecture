import PoincareLib.Geometry.CurveShortening.Ramp.Slope.C2.SlopePreservation

/-!
# Finite regularity of the corrected C2 ramp ratio

The actual regularized curvature and positive slope are C2 in the original
spatial labels. Closed periodicity and explicit interior time derivative
witnesses supply the other comparison hypotheses. Source: corrected
Lemma 19.14, MT2015Correction pp. 8-9; see
`2026-09-21-c2-ratio-preservation.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- Positive regularization and a nonzero spatial slope give C2 regularity
of the actual ratio on an interior slice. Correction Lemma 19.14, pp. 8-9. -/
theorem c2_rampRatio_contDiff (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    {epsilon t : ℝ} (hepsilon : 0 < epsilon) (ht : t ∈ Ioo a T)
    (hu : ∀ x, m62Slope P c t x ≠ 0) :
    ContDiff ℝ 2 (m63RampRatio P c epsilon t) := by
  let := P.charts.chartedSpace
  exact ((c2_scalar_contDiff_of_local P.flow c hc hlocal ht).2.2 epsilon hepsilon).div
    (c2_slope_contDiff_of_local P hlocal c hc ht) hu

/-- The actual ratio is periodic at both endpoints for every real epsilon,
independently of its denominator's sign. Correction Lemma 19.14, pp. 8-9. -/
theorem c2_rampRatio_periodic (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) (hT : a < T)
    (epsilon : ℝ) {t : ℝ} (ht : t ∈ Icc a T) :
    Function.Periodic (m63RampRatio P c epsilon t) curvePeriod := by
  let := P.charts.chartedSpace
  intro x
  simp only [m63RampRatio, c2_regularized_periodic P.flow c hc hlocal hT epsilon ht x,
    c2_slope_periodic P c hc ht x]

/-- The actual C2 estimate records certify the numerator and denominator
time derivatives before the quotient rule is used. Correction pp. 8-9. -/
theorem c2_rampRatio_differentiableAt_time (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) {K0 K1 K2 : ℝ}
    (hE : M63C2CurveEstimates P.flow c T K0 K1 K2) (hS : M63C2SlopeLaws P c T K2)
    {epsilon t : ℝ} (hepsilon : 0 < epsilon) (ht : t ∈ Ioo a T) (x : ℝ)
    (hu : m62Slope P c t x ≠ 0) :
    DifferentiableAt ℝ (fun s => m63RampRatio P c epsilon s x) t :=
  (hE.regularized_time epsilon hepsilon t ht x).div
    (hS.evolution t ht x).differentiableAt hu

end PoincareMT.M63
