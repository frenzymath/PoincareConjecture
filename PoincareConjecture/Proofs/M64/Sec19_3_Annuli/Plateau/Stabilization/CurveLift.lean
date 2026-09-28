import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.HorizontalPullbackC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ConstantLift
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem auxiliaryCircle_curveVelocity_eq
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    {gamma : ℝ → M} {x : ℝ} (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x) :
    curveVelocity (auxiliaryCircleSection P q ∘ gamma) x =
      mfderiv (𝓡 n) (𝓡 (n + 1)) (auxiliaryCircleSection P q) (gamma x)
        (curveVelocity gamma x) :=
  mfderiv_comp_apply x ((auxiliaryCircle_section_contMDiff P q).mdifferentiableAt
    (by simp)) hgamma 1



theorem auxiliaryCircle_curveVelocity_split
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    {gamma : ℝ → M} {x : ℝ} (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x) :
    P.charts.split (auxiliaryCircleSection P q (gamma x))
      (curveVelocity (auxiliaryCircleSection P q ∘ gamma) x) = (curveVelocity gamma x, 0) := by
  rw [auxiliaryCircle_curveVelocity_eq P q hgamma]
  exact auxiliaryCircle_section_mfderiv_split P q _ _



theorem auxiliaryCircle_curveSpeed_eq
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    (c : ℝ → ℝ → M) (time x : ℝ)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y time) x) :
    curveSpeed P.flow (fun y t => auxiliaryCircleSection P q (c y t)) time x =
      curveSpeed F c time x := by
  unfold curveSpeed RiemannianMetric.tangentNorm
  erw [auxiliaryCircle_curveVelocity_eq P q hc]
  exact congrArg Real.sqrt (auxiliaryCircle_section_metric P time q _ _ _)



theorem auxiliaryCircle_unitTangent_split
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    (c : ℝ → ℝ → M) (time x : ℝ)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y time) x) :
    P.charts.split (auxiliaryCircleSection P q (c x time))
      (spatialUnitTangent P.flow (fun y t => auxiliaryCircleSection P q (c y t)) time x) =
        (spatialUnitTangent F c time x, 0) := by
  unfold spatialUnitTangent
  rw [auxiliaryCircle_curveSpeed_eq P q c time x hc, map_smul]
  erw [auxiliaryCircle_curveVelocity_split P q hc]
  simp only [Prod.smul_mk, smul_zero]



theorem auxiliaryCircle_curvatureVector_split
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    (c : ℝ → ℝ → M) (time : ℝ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => c y time))
    (himm : ∀ x, curveVelocity (n := n) (fun y => c y time) x ≠ 0) (x : ℝ) :
    P.charts.split (auxiliaryCircleSection P q (c x time))
      (m62CurvatureVector P.flow (fun y t => auxiliaryCircleSection P q (c y t)) time x) =
        (m62CurvatureVector F c time x, 0) := by
  let d := fun y t => auxiliaryCircleSection P q (c y t)
  have hdiff (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun z => c z time) y :=
    hc.mdifferentiableAt (by norm_num)
  have hd : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 (fun y => d y time) :=
    ((auxiliaryCircle_section_contMDiff P q).of_le (by simp)).comp
      (hc.of_le (by norm_num))
  have hY := M63.unitTangent_contMDiff_of_c2 F c hc himm
  have heq : spatialUnitTangent P.flow d time =
      (fun y => (P.charts.split (d y time)).symm (spatialUnitTangent F c time y, 0)) := by
    funext y
    apply (P.charts.split (d y time)).injective
    rw [(P.charts.split (d y time)).apply_symm_apply]
    exact auxiliaryCircle_unitTangent_split P q c time y (hdiff y)
  change P.charts.split (d x time) (m62CurvatureVector P.flow d time x) = _
  unfold m62CurvatureVector m62SpatialDerivative
  rw [show curveSpeed P.flow d time x = curveSpeed F c time x from
    auxiliaryCircle_curveSpeed_eq P q c time x (hdiff x), map_smul, heq,
    auxiliaryCircle_horizontal_pullback_c1 P time hd hY x]
  simp only [Prod.smul_mk, smul_zero]
  rfl



theorem auxiliaryCircle_curvatureVector_eq
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    (c : ℝ → ℝ → M) (time : ℝ)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => c y time))
    (himm : ∀ x, curveVelocity (n := n) (fun y => c y time) x ≠ 0) (x : ℝ) :
    m62CurvatureVector P.flow (fun y t => auxiliaryCircleSection P q (c y t)) time x =
      mfderiv (𝓡 n) (𝓡 (n + 1)) (auxiliaryCircleSection P q) (c x time)
        (m62CurvatureVector F c time x) := by
  apply (P.charts.split (auxiliaryCircleSection P q (c x time))).injective
  rw [auxiliaryCircle_curvatureVector_split P q c time hc himm x]
  exact (auxiliaryCircle_section_mfderiv_split P q _ _).symm

end PoincareConjecture.M64
