import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.CurveLift













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem constantLift_immersed
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    ∀ x, curveVelocity (n := n + 1) (auxiliaryCircleSection P q ∘ gamma) x ≠ 0 := by
  intro x hx
  have hsplit := auxiliaryCircle_curveVelocity_split P q
    (hgamma.mdifferentiableAt (by norm_num) (x := x))
  rw [hx, map_zero] at hsplit
  exact himm x (congrArg Prod.fst hsplit).symm



theorem constantLift_curvature
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) (x : ℝ) :
    m62Curvature P.flow (fun y _ => auxiliaryCircleSection P q (gamma y)) time x =
      m62Curvature F (fun y _ => gamma y) time x := by
  unfold m62Curvature m62CurvatureSquared
  rw [auxiliaryCircle_curvatureVector_eq P q (fun y _ => gamma y) time hgamma himm x]
  exact congrArg Real.sqrt (auxiliaryCircle_section_metric P time q _ _ _)



theorem constantLift_arcLength
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (alpha beta : ℝ) :
    m63ArcLength P.flow (fun y _ => auxiliaryCircleSection P q (gamma y))
        time alpha beta = m63ArcLength F (fun y _ => gamma y) time alpha beta := by
  unfold m63ArcLength
  apply intervalIntegral.integral_congr
  intro x _hx
  exact auxiliaryCircle_curveSpeed_eq P q (fun y _ => gamma y) time x
    (hgamma.mdifferentiableAt (by norm_num))



theorem constantLift_length
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma) :
    m62Length P.flow (fun y _ => auxiliaryCircleSection P q (gamma y)) time =
      m62Length F (fun y _ => gamma y) time :=
  constantLift_arcLength P q time hgamma 0 curvePeriod



theorem constantLift_arcTotalCurvature
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) (alpha beta : ℝ) :
    m63ArcTotalCurvature P.flow (fun y _ => auxiliaryCircleSection P q (gamma y))
        time alpha beta =
      m63ArcTotalCurvature F (fun y _ => gamma y) time alpha beta := by
  unfold m63ArcTotalCurvature
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only
  rw [constantLift_curvature P q time hgamma himm x,
    auxiliaryCircle_curveSpeed_eq P q (fun y _ => gamma y) time x
      (hgamma.mdifferentiableAt (by norm_num))]



theorem constantLift_totalCurvature
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) (time : ℝ)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    m62TotalCurvature P.flow (fun y _ => auxiliaryCircleSection P q (gamma y)) time =
      m62TotalCurvature F (fun y _ => gamma y) time :=
  constantLift_arcTotalCurvature P q time hgamma himm 0 curvePeriod

end PoincareConjecture.M64.RampTransport
