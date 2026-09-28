import PoincareConjecture.Proofs.M14.Sec6_2_SmoothGaugeSurface
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeAction
import PoincareConjecture.Proofs.M14.Sec6_2_OpenSurfaceFields










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))




theorem supportedBackwardGauge_weightedPair (x₀ : G.gaugeCover.spatial b)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hsrcSupport : ∀ t ∈ tsupport η, p.curve t ∈ U)
    {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) (hsrc : p.curve s ∈ U) :
    let α := fun z : ℝ × ℝ => supportedBackwardGaugeFamily p b lift η z.2 z.1
    2 * Real.sqrt s * G.spacetime.horizontalMetric.inner (α (s, 0))
      (surfaceHorizontalFst α s 0) (surfaceHorizontalSnd α s 0) =
      backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
        (s, (lift (p.curve s)).2.val) (deriv (fun t => (lift (p.curve t)).2.val) s) (η s) := by
  let α := fun z : ℝ × ℝ => supportedBackwardGaugeFamily p b lift η z.2 z.1
  let β := fun t => (G.gaugeCover.cylinder b).toSpacetime (lift (p.curve t))
  have hp := (p.curve_regular s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)
  have hL := (((hlift _ hsrc).contMDiffAt (hU.mem_nhds hsrc)).of_le (by simp)).comp s hp
  have hfirst : (fun t => α (t, 0)) =ᶠ[𝓝 s] β := by
    filter_upwards [hp.continuousAt.preimage_mem_nhds (hU.mem_nhds hsrc)] with t ht
    change supportedBackwardGaugeFamily p b lift η 0 t = β t
    rw [supportedBackwardGaugeFamily_at_zero p b lift η
      (fun r hr => hright _ (hsrcSupport r hr))]
    exact (hright _ ht).symm
  have hd := hfirst.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
  have hparameter := supportedBackwardGaugeFamily_parameter_mfderiv p b lift η
    (fun t ht => hright _ (hsrcSupport t ht)) s
  change mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (fun v => α (s, v)) 0 (1 : ℝ) = _ at hparameter
  have hvelocity := gaugeCurve_projectedVelocity b (fun t => (lift (p.curve t)).1)
    (fun t => (lift (p.curve t)).2) (hL.fst.mdifferentiableAt (by simp))
      (hL.snd.mdifferentiableAt (by simp))
  change projectedCurveVelocity G β s = _ at hvelocity
  change 2 * Real.sqrt s * G.spacetime.horizontalMetric.inner (α (s, 0))
    (surfaceHorizontalFst α s 0) (surfaceHorizontalSnd α s 0) = _
  unfold surfaceHorizontalFst surfaceHorizontalSnd
  rw [hd, hparameter, hfirst.eq_of_nhds]
  change 2 * Real.sqrt s * G.spacetime.horizontalMetric.inner (β s)
    (projectedCurveVelocity G β s)
    (G.spacetime.horizontalProjection (β s)
      (((G.gaugeCover.metric b).spatialTangentEquiv
        (lift (p.curve s)).1 (lift (p.curve s)).2 (η s)).val)) = _
  rw [hvelocity, G.spacetime.horizontalProjection_identity,
    ← (G.gaugeCover.metric b).metric_eq, backwardMetricCoefficient_apply,
    gaugeLift_time_eq p b lift hright (Ioo_subset_Icc_self hs) hsrc]

end PoincareConjecture.M14
