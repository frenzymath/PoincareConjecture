import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Exponential.InitialExponential
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold

/-!
# Initial frames of the actual comparison-coordinate exponentials

Differentiating the actual composition gives an orthonormal frame for
the normalized pullback metric at zero. Morgan--Tian, Claim 16.6,
pp. 371-372; see `derivations/19-normalized-exponential-family.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M44.NormalizedCapExponential

local notation "E" => StandardCapSpace

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta R : ℝ}
  {Q : SurgeryCapClose g₀ S g tip scale eta}

/-- The physical differential of the actual exponential is its supplied
initial chart frame, since the centered chart has identity differential.
Source: Claim 16.6, pp. 371-372. -/
theorem map_mfderiv_zero (D : NormalizedCapExponential Q R) :
    mfderiv (𝓡 3) (𝓡 3) D.map 0 = D.frame.toContinuousLinearMap := by
  have h0 : (0 : E) ∈ Metric.ball 0 R := Metric.mem_ball_self D.radius_pos
  have hm := (D.smooth.contMDiffAt (Metric.isOpen_ball.mem_nhds h0)).mdifferentiableAt (by simp)
  have hchart : MDifferentiableAt (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) tip) (D.map 0) := by
    rw [D.map_zero]
    exact mdifferentiableAt_extChartAt (mem_chart_source _ tip)
  have hd := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) 0 hchart hm
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ (fun v => extChartAt (𝓡 3) tip (D.map v)) 0 =
    (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) tip) (D.map 0)).comp
      (mfderiv (𝓡 3) (𝓡 3) D.map 0) at hd
  rw [D.initial_derivative.fderiv, D.map_zero, mfderiv_extChartAt_self,
    ContinuousLinearMap.id_comp] at hd
  exact hd.symm

/-- The actual comparison-coordinate initial frame is the inverse-chart
differential applied to the physical frame. Source: Claim 16.6, pp. 371-372. -/
theorem coordinateMap_fderiv_zero (D : NormalizedCapExponential Q R) :
    fderiv ℝ D.coordinateMap 0 =
      (mfderiv (𝓡 3) (𝓡 3) Q.inverse tip).comp D.frame.toContinuousLinearMap := by
  have h0 : (0 : E) ∈ Metric.ball 0 R := Metric.mem_ball_self D.radius_pos
  have hm := (D.smooth.contMDiffAt (Metric.isOpen_ball.mem_nhds h0)).mdifferentiableAt (by simp)
  have hi := (Q.inverse_smooth.contMDiffAt
    (Q.toPartialDiffeomorph.open_target.mem_nhds (D.map_mem 0 h0))).mdifferentiableAt (by simp)
  have hd := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) 0 hi hm
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ D.coordinateMap 0 =
    (mfderiv (𝓡 3) (𝓡 3) Q.inverse (D.map 0)).comp
      (mfderiv (𝓡 3) (𝓡 3) D.map 0) at hd
  rw [D.map_mfderiv_zero] at hd
  let invD : S.carrier → E →L[ℝ] E := fun p => mfderiv (𝓡 3) (𝓡 3) Q.inverse p
  have hpoint : (mfderiv (𝓡 3) (𝓡 3) Q.inverse (D.map 0) : E →L[ℝ] E) =
      mfderiv (𝓡 3) (𝓡 3) Q.inverse tip :=
    congrArg invD D.map_zero
  exact hd.trans (congrArg (fun A : E →L[ℝ] E => A.comp D.frame.toContinuousLinearMap) hpoint)

/-- The initial derivative of the actual inverse-chart exponential is
orthonormal for the actual normalized coefficients at zero.
Source: Claim 16.6, pp. 371-372. -/
theorem coordinate_frame_inner (D : NormalizedCapExponential Q R) (v w : E) :
    Q.normalizedCoefficients 0 (fderiv ℝ D.coordinateMap 0 v) (fderiv ℝ D.coordinateMap 0 w) =
      inner ℝ v w := by
  have h0 : (0 : E) ∈ g₀.metric.ball 0 eta⁻¹ := by
    rw [M36.standard_ball_eq_euclidean g₀ (inv_pos.mpr Q.eta_pos)]
    exact Metric.mem_ball_self ((M36.radialEuclideanRadius_pos_iff g₀ _).mpr
      (inv_pos.mpr Q.eta_pos))
  let e := Q.toPartialDiffeomorph
  have heD : e.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨e.mdifferentiableOn (by simp), e.symm.mdifferentiableOn (by simp)⟩
  have hcancel := heD.comp_symm_deriv (e.map_source h0)
  change (mfderiv (𝓡 3) (𝓡 3) Q.map (Q.inverse (Q.map 0))).comp
    (mfderiv (𝓡 3) (𝓡 3) Q.inverse (Q.map 0)) = ContinuousLinearMap.id ℝ E at hcancel
  rw [Q.left_inverse h0, Q.map_tip] at hcancel
  have hframe (a : E) : mfderiv (𝓡 3) (𝓡 3) Q.map 0
      (fderiv ℝ D.coordinateMap 0 a) = D.frame a := by
    rw [D.coordinateMap_fderiv_zero]
    exact congrArg (fun L => L (D.frame a)) hcancel
  rw [Q.normalizedCoefficients_apply, hframe v, hframe w]
  have hphysical := D.frame_inner v w
  rw [Q.normalizedMetric.chartCoefficients_self] at hphysical
  have hpoint := congrArg
    (fun p : S.carrier => scale⁻¹ ^ 2 * g.inner p (D.frame v) (D.frame w)) Q.map_tip
  exact hpoint.trans hphysical

end PoincareMT.M44.NormalizedCapExponential
