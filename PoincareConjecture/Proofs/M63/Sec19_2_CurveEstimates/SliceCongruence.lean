import PoincareConjecture.Statements.M63CurveEstimates











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) {c d : ℝ → ℝ → M} {t x : ℝ}



theorem curveSpeed_congr_slice (h : ∀ y, c y t = d y t) :
    curveSpeed F c t x = curveSpeed F d t x :=
  congrArg (fun gamma : ℝ → M => curveSpeed F (fun y _ => gamma y) t x) (funext h)



theorem curvatureSquared_congr_slice (h : ∀ y, c y t = d y t) :
    m62CurvatureSquared F c t x = m62CurvatureSquared F d t x :=
  congrArg (fun gamma : ℝ → M => m62CurvatureSquared F (fun y _ => gamma y) t x)
    (funext h)



theorem curvature_congr_slice (h : ∀ y, c y t = d y t) :
    m62Curvature F c t x = m62Curvature F d t x :=
  congrArg (fun gamma : ℝ → M => m62Curvature F (fun y _ => gamma y) t x) (funext h)



theorem regularizedCurvature_congr_slice (h : ∀ y, c y t = d y t) (epsilon : ℝ) :
    m62RegularizedCurvature F c epsilon t x = m62RegularizedCurvature F d epsilon t x :=
  congrArg (fun gamma : ℝ → M =>
    m62RegularizedCurvature F (fun y _ => gamma y) epsilon t x) (funext h)



theorem tangentRicci_congr_slice (h : ∀ y, c y t = d y t) :
    m62TangentRicci F c t x = m62TangentRicci F d t x :=
  congrArg (fun gamma : ℝ → M => m62TangentRicci F (fun y _ => gamma y) t x) (funext h)



theorem arcDerivative_congr_slice (h : ∀ y, c y t = d y t) (f : ℝ → ℝ) :
    m62ArcDerivative F c t f x = m62ArcDerivative F d t f x :=
  congrArg (fun gamma : ℝ → M => m62ArcDerivative F (fun y _ => gamma y) t f x)
    (funext h)



theorem arcSecondDerivative_congr_slice (h : ∀ y, c y t = d y t) (f : ℝ → ℝ) :
    m62ArcSecondDerivative F c t f x = m62ArcSecondDerivative F d t f x :=
  congrArg (fun gamma : ℝ → M => m62ArcSecondDerivative F (fun y _ => gamma y) t f x)
    (funext h)



theorem length_congr_slice (h : ∀ y, c y t = d y t) : m62Length F c t = m62Length F d t :=
  congrArg (fun gamma : ℝ → M => m62Length F (fun y _ => gamma y) t) (funext h)



theorem totalCurvature_congr_slice (h : ∀ y, c y t = d y t) :
    m62TotalCurvature F c t = m62TotalCurvature F d t :=
  congrArg (fun gamma : ℝ → M => m62TotalCurvature F (fun y _ => gamma y) t) (funext h)



theorem regularizedTotalCurvature_congr_slice (h : ∀ y, c y t = d y t) (epsilon : ℝ) :
    m62RegularizedTotalCurvature F c epsilon t = m62RegularizedTotalCurvature F d epsilon t :=
  congrArg (fun gamma : ℝ → M =>
    m62RegularizedTotalCurvature F (fun y _ => gamma y) epsilon t) (funext h)

section CircleProduct

variable {F' : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
  (P : M62.CircleProductData F' circumference) {c d : ℝ → ℝ → P.charts.Point}



theorem slope_congr_slice (h : ∀ y, c y t = d y t) :
    m62Slope P c t x = m62Slope P d t x :=
  congrArg (fun gamma : ℝ → P.charts.Point => m62Slope P (fun y _ => gamma y) t x)
    (funext h)



theorem rampRatio_congr_slice (h : ∀ y, c y t = d y t) (epsilon : ℝ) :
    m63RampRatio P c epsilon t x = m63RampRatio P d epsilon t x :=
  congrArg (fun gamma : ℝ → P.charts.Point =>
    m63RampRatio P (fun y _ => gamma y) epsilon t x) (funext h)

end CircleProduct

end PoincareConjecture.M63
