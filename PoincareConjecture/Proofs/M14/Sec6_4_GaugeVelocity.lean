import PoincareConjecture.Proofs.M14.Sec6_2_GaugeCurve
import PoincareConjecture.Proofs.M14.Sec6_2_SquareRootVelocityExtension










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)




theorem gauge_projectedDifferential
    (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x : G.gaugeCover.spatial b)
    (v : TangentSpace (spacetimeModel n) (t, x)) :
    G.spacetime.horizontalProjection ((G.gaugeCover.cylinder b).toSpacetime (t, x))
      (mfderiv (spacetimeModel n) (spacetimeModel n)
        (G.gaugeCover.cylinder b).toSpacetime (t, x) v) =
      (G.gaugeCover.metric b).spatialTangentEquiv t x v.2 := by
  let D := G.timeIntervals.interval (G.gaugeCover.interval b)
  have ht : v.1 = D.inclusionDerivative t v.1 • D.positiveTangent t := by
    apply (D.inclusionDerivative t).injective
    simp only [map_smul, SmoothSpacetimeInterval.positiveTangent,
      ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have hd := mfderiv_prod_eq_add_apply (p := (t, x))
    ((G.gaugeCover.cylinder b).smooth.mdifferentiableAt (by simp)) (v := (v.1, v.2))
  rw [ht, map_smul, (G.gaugeCover.cylinder b).worldline_derivative,
    ← (G.gaugeCover.metric b).spatialTangentEquiv_eq] at hd
  change G.spacetime.horizontalProjection _
    (mfderiv (spacetimeModel n) (spacetimeModel n)
      (G.gaugeCover.cylinder b).toSpacetime (t, x) (v.1, v.2)) = _
  rw [ht, hd, map_add, map_smul, horizontalProjection_timeVector_eq_zero,
    smul_zero, zero_add, G.spacetime.horizontalProjection_identity]




theorem gaugeCurve_projectedVelocityWithin
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b} {J : Set ℝ} {s : ℝ}
    (hβ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) β J s)
    (hJ : UniqueDiffWithinAt ℝ J s) :
    projectedCurveVelocityWithin G (fun r => (G.gaugeCover.cylinder b).toSpacetime (β r)) J s =
      (G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin (fun r => (β r).2.val) J s) := by
  have hd := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp_mfderivWithin s
      ((G.gaugeCover.cylinder b).smooth.mdifferentiableAt (by simp))
      hβ hJ.uniqueMDiffWithinAt)
  have hsp := congrArg (fun L => (L (1 : ℝ)).2)
    (mfderivWithin_prodMk hβ.fst hβ.snd hJ.uniqueMDiffWithinAt)
  change (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) β J s (1 : ℝ)).2 =
    mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) (fun r => (β r).2) J s (1 : ℝ) at hsp
  rw [(G.gaugeCover.spatial b).mfderivWithin_curve_eq_derivWithin_val hβ.snd hJ] at hsp
  unfold projectedCurveVelocityWithin
  dsimp only [Function.comp_def, ContinuousLinearMap.comp_apply] at hd
  erw [hd, gauge_projectedDifferential b, hsp]

private theorem projected_tangent_heq {q r : G.Point} (h : q = r)
    {v : TangentSpace (spacetimeModel n) q} {w : TangentSpace (spacetimeModel n) r}
    (hv : HEq v w) :
    HEq (G.spacetime.horizontalProjection q v) (G.spacetime.horizontalProjection r w) := by
  cases h
  cases hv
  rfl




theorem projectedCurveVelocityWithin_congrOn {γ β : ℝ → G.Point} {J : Set ℝ}
    (h : EqOn γ β J) {s : ℝ} (hs : s ∈ J) :
    HEq (projectedCurveVelocityWithin G γ J s) (projectedCurveVelocityWithin G β J s) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n) h hs
  unfold projectedCurveVelocityWithin
  apply projected_tangent_heq (G := G) (h hs)
  exact heq_of_eq (congrArg (fun L => L (1 : ℝ)) hd)

end PoincareConjecture.M14
