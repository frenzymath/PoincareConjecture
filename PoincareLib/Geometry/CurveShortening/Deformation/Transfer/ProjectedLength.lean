import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Angular
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.Continuity
import PoincareLib.Geometry.CurveShortening.Ramp.Family

/-!
# Length decreases under the actual base projection

The first step of Morgan--Tian Claim 19.32, printed p. 463. The retained
product metric and tangent splitting give the pointwise speed comparison.
Continuity of both actual speeds justifies integration, including endpoints.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}

/-- The spatial component of the genuine product metric has no greater
norm; Claim 19.32, printed p. 463. -/
theorem m65Projection_tangentNorm_le (P : M62.CircleProductData F circumference)
    (t : ℝ) (q : P.charts.Point) (v : TangentSpace (𝓡 (n + 1)) q) :
    (F.metric t).tangentNorm q.1 (P.charts.split q v).1 ≤
      (P.flow.metric t).tangentNorm q v := by
  unfold RiemannianMetric.tangentNorm
  apply Real.sqrt_le_sqrt
  rw [P.metric_eq]
  exact le_add_of_nonneg_right
    ((P.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)

/-- The actual derivative of projection identifies its speed with the
spatial component of product velocity; Claim 19.32, printed p. 463. -/
theorem m65Projection_speed_le (P : M62.CircleProductData F circumference)
    (gamma : ℝ → P.charts.Point) {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma x) (t : ℝ) :
    (F.metric t).tangentNorm (gamma x).1
        (curveVelocity (fun y => (gamma y).1) x) ≤
      (P.flow.metric t).tangentNorm (gamma x) (curveVelocity gamma x) := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hchain := mfderiv_comp_apply (f := gamma) (g := (Prod.fst : P.charts.Point → M))
    x (hfst.mdifferentiableAt (by simp)) hgamma (1 : ℝ)
  change curveVelocity (fun y => (gamma y).1) x =
    mfderiv (𝓡 (n + 1)) (𝓡 n) (Prod.fst : P.charts.Point → M)
      (gamma x) (curveVelocity gamma x) at hchain
  rw [← P.charts.split_space] at hchain
  rw [hchain]
  exact m65Projection_tangentNorm_le P t (gamma x) (curveVelocity gamma x)

/-- Projection decreases the length of the exact C1 loop in the selected
family at every included time; Claim 19.32, printed p. 463. -/
theorem m65ProjectedFamilyLength_le
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta circumference : ℝ} {P : M62.CircleProductData F circumference}
    {approximation : M63RawApproximation F Gamma zeta}
    (S : M63ProductSolutionFamily P approximation) (t : Set.Icc a b) (z : LoopTwoSphere) :
    freeLoopLength (F.metric t) (S.projected t z) ≤ m62Length P.flow (S.curve z) t := by
  unfold freeLoopLength m62Length
  apply intervalIntegral.integral_mono_on (by unfold curvePeriod; positivity)
    ((Proofs.M58.continuous_freeLoopSpeed (F.metric t) (S.projected t z)).intervalIntegrable _ _)
    (M62.length_integrable P.flow (S.curve z) (S.shrinking z) t.2)
  intro x _
  rw [funext (S.projected_eq t z)]
  exact m65Projection_speed_le P (fun y => S.curve z y t)
    ((S.shrinking z).spatial_regular t t.2 |>.mdifferentiableAt (by simp)) t

end PoincareMT
