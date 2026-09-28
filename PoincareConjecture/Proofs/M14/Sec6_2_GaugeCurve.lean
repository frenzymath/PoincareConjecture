import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetVelocity
import PoincareConjecture.Proofs.M14.Sec6_2_CurveVelocity

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
  (u : ℝ → G.gaugeCover.spatial b)

theorem gaugeCurve_projectedVelocity {s : ℝ}
    (hθ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ s)
    (hu : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) u s) :
    projectedCurveVelocity G (fun t => (G.gaugeCover.cylinder b).toSpacetime (θ t, u t)) s =
      (G.gaugeCover.metric b).spatialTangentEquiv (θ s) (u s)
        (deriv (fun t => (u t).val) s) := by
  let D := G.timeIntervals.interval (G.gaugeCover.interval b)
  let e := G.gaugeCover.cylinder b
  let vt := mfderiv (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ s (1 : ℝ)
  have htangent : vt = D.inclusionDerivative (θ s) vt • D.positiveTangent (θ s) := by
    apply (D.inclusionDerivative (θ s)).injective
    simp only [map_smul, SmoothSpacetimeInterval.positiveTangent,
      ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  have he : MDifferentiableAt (spacetimeModel n) (spacetimeModel n)
      e.toSpacetime (θ s, u s) := e.smooth.mdifferentiableAt (by simp)
  have hd := mfderiv_comp_apply s he (hθ.prodMk hu) (1 : ℝ)
  rw [mfderiv_prodMk hθ hu] at hd
  change mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n)
    (fun t => e.toSpacetime (θ t, u t)) s (1 : ℝ) =
      mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (θ s, u s)
        (vt, mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) u s (1 : ℝ)) at hd
  rw [mfderiv_prod_eq_add_apply he, htangent, map_smul, e.worldline_derivative,
    ← (G.gaugeCover.metric b).spatialTangentEquiv_eq,
    (G.gaugeCover.spatial b).mfderiv_curve_eq_deriv_val hu] at hd
  have hzero : G.spacetime.horizontalProjection (e.toSpacetime (θ s, u s))
      (G.spacetime.timeVector (e.toSpacetime (θ s, u s))) = 0 := by
    apply Subtype.ext
    simp only [G.spacetime.horizontalProjection_eq, G.spacetime.timeVector_normalized,
      one_smul, sub_self, ZeroMemClass.coe_zero]
  unfold projectedCurveVelocity
  rw [hd, map_add, map_smul, hzero, smul_zero, zero_add,
    G.spacetime.horizontalProjection_identity]

theorem gaugeCurve_rawLIntegrand {s : ℝ}
    (hθ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ s)
    (hu : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) u s) :
    M14RawLIntegrand G (fun t => (G.gaugeCover.cylinder b).toSpacetime (θ t, u t))
      (projectedCurveVelocity G
        (fun t => (G.gaugeCover.cylinder b).toSpacetime (θ t, u t))) s =
      Real.sqrt s *
        (horizontalScalarCurvature G.leafwise ((G.gaugeCover.cylinder b).toSpacetime (θ s, u s)) +
        ((G.gaugeCover.metric b).metric (θ s).val).inner (u s)
          (deriv (fun t => (u t).val) s) (deriv (fun t => (u t).val) s)) := by
  unfold M14RawLIntegrand
  rw [gaugeCurve_projectedVelocity b θ u hθ hu, ← (G.gaugeCover.metric b).metric_eq]

end PoincareConjecture.M14
