import PoincareConjecture.Proofs.M14.OrdinaryCaptureAction
import PoincareConjecture.Proofs.M14.Sec6_4_GaugeVelocity










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {K : SpacetimeInterval}
  (e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C)
  (g : SpacetimeCylinderMetric e)



theorem ordinaryCapture_projectedDifferential
    (t : (G.timeIntervals.interval K).Point) (c : C)
    (v : TangentSpace (spacetimeModel n) (t, c)) :
    G.spacetime.horizontalProjection (e.toSpacetime (t, c))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, c) v) =
      g.spatialTangentEquiv t c v.2 := by
  let J := G.timeIntervals.interval K
  have ht : v.1 = J.inclusionDerivative t v.1 • J.positiveTangent t := by
    apply (J.inclusionDerivative t).injective
    simp only [map_smul, SmoothSpacetimeInterval.positiveTangent,
      ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hd := mfderiv_prod_eq_add_apply (p := (t, c))
    (e.smooth.mdifferentiableAt (by simp)) (v := (v.1, v.2))
  rw [ht, map_smul, e.worldline_derivative, ← g.spatialTangentEquiv_eq] at hd
  change G.spacetime.horizontalProjection _
    (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, c) (v.1, v.2)) = _
  rw [ht, hd, map_add, map_smul, horizontalProjection_timeVector_eq_zero,
    smul_zero, zero_add, G.spacetime.horizontalProjection_identity]




theorem ordinaryCapture_cylinderVelocityWithin
    (θ : ℝ → (G.timeIntervals.interval K).Point) (q : ℝ → C)
    {S : Set ℝ} {s : ℝ}
    (hθ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ S s)
    (hq : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (𝓡 n) q S s)
    (hS : UniqueDiffWithinAt ℝ S s) :
    projectedCurveVelocityWithin G (fun r => e.toSpacetime (θ r, q r)) S s =
      g.spatialTangentEquiv (θ s) (q s) (curveVelocityWithin q S s) := by
  have hβ := hθ.prodMk hq
  have hd := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp_mfderivWithin s (e.smooth.mdifferentiableAt (by simp))
      hβ hS.uniqueMDiffWithinAt)
  have hsp := congrArg (fun L => (L (1 : ℝ)).2)
    (mfderivWithin_prodMk hθ hq hS.uniqueMDiffWithinAt)
  change (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n)
    (fun r => (θ r, q r)) S s 1).2 = curveVelocityWithin q S s at hsp
  unfold projectedCurveVelocityWithin
  dsimp only [Function.comp_def, ContinuousLinearMap.comp_apply] at hd
  erw [hd, ordinaryCapture_projectedDifferential e g, hsp]

end PoincareConjecture.M14
