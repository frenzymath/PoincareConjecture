import PoincareConjecture.Proofs.M14.Sec6_3_GaugeBlend
import PoincareConjecture.Proofs.M14.Sec6_2_PotentialCoefficient

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

open Proofs.M09

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)
  (α β : ℝ → G.Point) (x₀ : G.gaugeCover.spatial b)

theorem gaugeBlend_quadraticDensity {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    {T a d s : ℝ}
    (hα : ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 α s)
    (hβ : ContMDiffAt (𝓘(ℝ, ℝ)) (spacetimeModel n) 1 β s)
    (hαU : α s ∈ U) (hβU : β s ∈ U)
    (hmem : smoothJoinBlend (fun t => (lift (α t)).2.val)
      (fun t => (lift (β t)).2.val) a d s ∈ G.gaugeCover.spatial b)
    (hclock : (lift (β s)).1.val = T - s) :
    let v := smoothJoinBlend (fun t => (lift (α t)).2.val)
      (fun t => (lift (β t)).2.val) a d
    M14RawLIntegrand G (gaugeBlend b lift α β a d)
      (projectedCurveVelocity G (gaugeBlend b lift α β a d)) s =
      backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
        (s, v s) (deriv v s) (deriv v s) / 2 +
      backwardPotentialCoefficient b (fun t => (lift (β t)).1) x₀ (s, v s) := by
  dsimp only
  have hA := (((hlift _ hαU).contMDiffAt (hU.mem_nhds hαU)).of_le (by simp)).comp s hα
  have hB := (((hlift _ hβU).contMDiffAt (hU.mem_nhds hβU)).of_le (by simp)).comp s hβ
  have hAv : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun t => (lift (α t)).2.val) s :=
    contMDiff_subtype_val.contMDiffAt.comp s hA.snd
  have hBv : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun t => (lift (β t)).2.val) s :=
    contMDiff_subtype_val.contMDiffAt.comp s hB.snd
  have hχ : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1
      (fun t => smoothJoinCutoff ((t - a) / d)) s :=
    ((smoothJoinCutoff_contDiff.of_le (by simp)).comp
      ((contDiff_id.sub contDiff_const).div_const d)).contMDiff.contMDiffAt
  have hshift := hχ.smul (hBv.sub hAv)
  have hspace := ((((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hmem).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hmem)).of_le
      (by simp : (1 : ℕ∞ω) ≤ ∞)).comp s (hA.snd.prodMk hshift)
  have hv := hAv.add hshift
  have heq : (fun t => ((G.gaugeCover.spatial b).affineShift (lift (α t)).2
      (smoothJoinCutoff ((t - a) / d) •
        ((lift (β t)).2.val - (lift (α t)).2.val))).val) =ᶠ[𝓝 s]
      smoothJoinBlend (fun t => (lift (α t)).2.val)
        (fun t => (lift (β t)).2.val) a d := by
    filter_upwards [hv.continuousAt.preimage_mem_nhds
      ((G.gaugeCover.spatial b).isOpen.mem_nhds hmem)] with t ht
    exact (G.gaugeCover.spatial b).affineShift_val ht
  have hden := gaugeCurve_quadraticDensity b (fun t => (lift (β t)).1) x₀
    (fun t => (G.gaugeCover.spatial b).affineShift (lift (α t)).2
      (smoothJoinCutoff ((t - a) / d) • ((lift (β t)).2.val - (lift (α t)).2.val)))
    (hB.fst.mdifferentiableAt (by simp)) (hspace.mdifferentiableAt (by simp)) hclock
  unfold gaugeBlend
  simpa only [heq.eq_of_nhds, heq.deriv_eq] using hden

end PoincareConjecture.M14
