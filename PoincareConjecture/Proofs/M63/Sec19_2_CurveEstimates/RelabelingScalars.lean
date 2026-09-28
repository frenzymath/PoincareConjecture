import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import PoincareConjecture.Statements.M63CurveEstimates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (d : ℝ → ℝ → M)
  {phi : ℝ → ℝ} {t x : ℝ}



theorem curvatureSquared_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) :
    m62CurvatureSquared F (fun y s => d (phi y) s) t x =
      m62CurvatureSquared F d t (phi x) := by
  unfold m62CurvatureSquared
  rw [curvatureVector_comp F d hd hphi hpos hS]



theorem curvature_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) :
    m62Curvature F (fun y s => d (phi y) s) t x = m62Curvature F d t (phi x) := by
  unfold m62Curvature
  rw [curvatureSquared_comp F d hd hphi hpos hS]



theorem regularizedCurvature_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) (epsilon : ℝ) :
    m62RegularizedCurvature F (fun y s => d (phi y) s) epsilon t x =
      m62RegularizedCurvature F d epsilon t (phi x) := by
  unfold m62RegularizedCurvature
  rw [curvatureSquared_comp F d hd hphi hpos hS]



theorem tangentRicci_comp
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t) (phi x))
    (hphi : DifferentiableAt ℝ phi x) (hpos : 0 < deriv phi x) :
    m62TangentRicci F (fun y s => d (phi y) s) t x =
      m62TangentRicci F d t (phi x) := by
  unfold m62TangentRicci
  rw [spatialUnitTangent_comp F d hd hphi.hasDerivAt hpos]



theorem arcDerivative_comp {f : ℝ → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t) (phi x))
    (hphi : DifferentiableAt ℝ phi x) (hpos : 0 < deriv phi x)
    (hf : DifferentiableAt ℝ f (phi x)) :
    m62ArcDerivative F (fun y s => d (phi y) s) t (fun y => f (phi y)) x =
      m62ArcDerivative F d t f (phi x) := by
  unfold m62ArcDerivative
  have hcomp : deriv (fun y => f (phi y)) x = deriv f (phi x) * deriv phi x :=
    deriv_comp x hf hphi
  rw [curveSpeed_comp F d hd hphi.hasDerivAt hpos.le, hcomp]
  rw [mul_inv_rev]
  calc
    (curveSpeed F d t (phi x))⁻¹ * (deriv phi x)⁻¹ * (deriv f (phi x) * deriv phi x) =
        (curveSpeed F d t (phi x))⁻¹ * deriv f (phi x) *
          ((deriv phi x)⁻¹ * deriv phi x) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hpos.ne', mul_one]




theorem arcSecondDerivative_comp {f : ℝ → ℝ}
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hf : ∀ y, DifferentiableAt ℝ f (phi y))
    (hDf : DifferentiableAt ℝ (m62ArcDerivative F d t f) (phi x)) :
    m62ArcSecondDerivative F (fun y s => d (phi y) s) t (fun y => f (phi y)) x =
      m62ArcSecondDerivative F d t f (phi x) := by
  have hfirst : m62ArcDerivative F (fun y s => d (phi y) s) t (fun y => f (phi y)) =
      fun y => m62ArcDerivative F d t f (phi y) :=
    funext fun y => arcDerivative_comp F d (hd (phi y)) (hphi y) (hpos y) (hf y)
  unfold m62ArcSecondDerivative
  rw [hfirst]
  exact arcDerivative_comp F d (hd (phi x)) (hphi x) (hpos x) hDf

section CircleProduct

variable {F' : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
  (P : M62.CircleProductData F' circumference) (c : ℝ → ℝ → P.charts.Point)



theorem slope_comp
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun y => c y t) (phi x))
    (hphi : DifferentiableAt ℝ phi x) (hpos : 0 < deriv phi x) :
    m62Slope P (fun y s => c (phi y) s) t x = m62Slope P c t (phi x) := by
  let := P.charts.chartedSpace
  unfold m62Slope
  rw [spatialUnitTangent_comp P.flow c hc hphi.hasDerivAt hpos]



theorem rampRatio_comp
    (hc : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun y => c y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
      (fun y => (⟨c y t, spatialUnitTangent P.flow c t y⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point)) (phi x)) (epsilon : ℝ) :
    m63RampRatio P (fun y s => c (phi y) s) epsilon t x =
      m63RampRatio P c epsilon t (phi x) := by
  let := P.charts.chartedSpace
  unfold m63RampRatio
  rw [regularizedCurvature_comp P.flow c hc hphi hpos hS,
    slope_comp P c (hc (phi x)) (hphi x) (hpos x)]

end CircleProduct

end PoincareConjecture.M63
