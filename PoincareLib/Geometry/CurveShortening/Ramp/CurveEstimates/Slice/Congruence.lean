import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates

/-!
# Equality of actual spatial quantities on equal slices

Every displayed scalar and spatial integral depends only on the entire
parameterized slice and the actual ambient data at that time. These
substitutions support fixed-label transport on a time slab without asserting
equality outside it. Source: MT2007 Lemma 19.6, pp. 441-442, and correction
pp. 6-8; see `2026-09-21-relabeling-differential.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) {c d : ℝ → ℝ → M} {t x : ℝ}

/-- Equal parameterized slices have equal actual speed, without a regularity
premise. This is substitution in Lemma 19.6's geometry, MT2007 p. 441. -/
theorem curveSpeed_congr_slice (h : ∀ y, c y t = d y t) :
    curveSpeed F c t x = curveSpeed F d t x :=
  congrArg (fun gamma : ℝ → M => curveSpeed F (fun y _ => gamma y) t x) (funext h)

/-- Equal entire slices give equal actual squared curvature, including the
totalized spatial derivatives. MT2007 Lemma 19.6, pp. 441-442. -/
theorem curvatureSquared_congr_slice (h : ∀ y, c y t = d y t) :
    m62CurvatureSquared F c t x = m62CurvatureSquared F d t x :=
  congrArg (fun gamma : ℝ → M => m62CurvatureSquared F (fun y _ => gamma y) t x)
    (funext h)

/-- Curvature norms agree on equal entire slices, also at curvature zeros.
MT2015Correction Corollary 0.3, pp. 6-7. -/
theorem curvature_congr_slice (h : ∀ y, c y t = d y t) :
    m62Curvature F c t x = m62Curvature F d t x :=
  congrArg (fun gamma : ℝ → M => m62Curvature F (fun y _ => gamma y) t x) (funext h)

/-- Equal slices have equal regularized curvature for every real epsilon.
MT2015Correction Corollary 0.3, pp. 6-7. -/
theorem regularizedCurvature_congr_slice (h : ∀ y, c y t = d y t) (epsilon : ℝ) :
    m62RegularizedCurvature F c epsilon t x = m62RegularizedCurvature F d epsilon t x :=
  congrArg (fun gamma : ℝ → M =>
    m62RegularizedCurvature F (fun y _ => gamma y) epsilon t x) (funext h)

/-- The actual connection and unit tangent give the same Ricci scalar on
equal slices. MT2007 Lemma 19.6, pp. 441-442. -/
theorem tangentRicci_congr_slice (h : ∀ y, c y t = d y t) :
    m62TangentRicci F c t x = m62TangentRicci F d t x :=
  congrArg (fun gamma : ℝ → M => m62TangentRicci F (fun y _ => gamma y) t x) (funext h)

/-- For a fixed scalar field, the arc derivative agrees on equal slices.
MT2007 Lemma 19.6, pp. 441-442. -/
theorem arcDerivative_congr_slice (h : ∀ y, c y t = d y t) (f : ℝ → ℝ) :
    m62ArcDerivative F c t f x = m62ArcDerivative F d t f x :=
  congrArg (fun gamma : ℝ → M => m62ArcDerivative F (fun y _ => gamma y) t f x)
    (funext h)

/-- The iterated arc derivative retains the same varying speed on equal
entire slices. MT2007 Claim 19.11, p. 446. -/
theorem arcSecondDerivative_congr_slice (h : ∀ y, c y t = d y t) (f : ℝ → ℝ) :
    m62ArcSecondDerivative F c t f x = m62ArcSecondDerivative F d t f x :=
  congrArg (fun gamma : ℝ → M => m62ArcSecondDerivative F (fun y _ => gamma y) t f x)
    (funext h)

/-- Actual length agrees on equal parameterized slices.
MT2007 Lemma 19.9, p. 445; correction Lemma 0.4, pp. 7-8. -/
theorem length_congr_slice (h : ∀ y, c y t = d y t) : m62Length F c t = m62Length F d t :=
  congrArg (fun gamma : ℝ → M => m62Length F (fun y _ => gamma y) t) (funext h)

/-- Actual total curvature agrees on equal parameterized slices.
MT2015Correction Lemma 0.4, pp. 7-8. -/
theorem totalCurvature_congr_slice (h : ∀ y, c y t = d y t) :
    m62TotalCurvature F c t = m62TotalCurvature F d t :=
  congrArg (fun gamma : ℝ → M => m62TotalCurvature F (fun y _ => gamma y) t) (funext h)

/-- Actual regularized total curvature agrees on equal slices.
MT2015Correction Lemma 0.4, pp. 7-8. -/
theorem regularizedTotalCurvature_congr_slice (h : ∀ y, c y t = d y t) (epsilon : ℝ) :
    m62RegularizedTotalCurvature F c epsilon t = m62RegularizedTotalCurvature F d epsilon t :=
  congrArg (fun gamma : ℝ → M =>
    m62RegularizedTotalCurvature F (fun y _ => gamma y) epsilon t) (funext h)

section CircleProduct

variable {F' : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
  (P : M62.CircleProductData F' circumference) {c d : ℝ → ℝ → P.charts.Point}

/-- The actual unit-circle pairing agrees on equal entire slices.
Claim 19.11, MT2007 p. 446. -/
theorem slope_congr_slice (h : ∀ y, c y t = d y t) :
    m62Slope P c t x = m62Slope P d t x :=
  congrArg (fun gamma : ℝ → P.charts.Point => m62Slope P (fun y _ => gamma y) t x)
    (funext h)

/-- The actual corrected quotient agrees on equal slices without a slope
sign premise. Corrected Lemma 19.14, MT2015Correction pp. 8-9. -/
theorem rampRatio_congr_slice (h : ∀ y, c y t = d y t) (epsilon : ℝ) :
    m63RampRatio P c epsilon t x = m63RampRatio P d epsilon t x :=
  congrArg (fun gamma : ℝ → P.charts.Point =>
    m63RampRatio P (fun y _ => gamma y) epsilon t x) (funext h)

end CircleProduct

end PoincareMT.M63
