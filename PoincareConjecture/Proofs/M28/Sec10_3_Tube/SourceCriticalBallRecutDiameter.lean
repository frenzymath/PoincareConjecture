import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallDistanceBound
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveRecutDiameter











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in





theorem exists_retained_recut_diameter_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (_D0 : LeviCivitaData G.limitMetric)
            (L : EpsilonNeck G.limitMetric) (j : ℕ), L.center = G.base →
            L.carrier ⊆ G.exhaustion j →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              ∀ X : Set G.limitCarrier.carrier,
                (∀ x ∈ X, ∀ᶠ k in atTop, (G.embedding (sigma k) x).val.val ∉
                  ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                    (f k)) →
                ∀ (N : EpsilonNeck G.limitMetric) (Q : Set G.limitCarrier.carrier),
                  IsOpen Q → Q ⊆ X \ N.central_sphere →
                  closure Q = Q ∪ N.central_sphere →
                  ∀ a b : ℝ, a < 0 → 0 < b →
                    ∀ V : TopologicalSpace.Opens G.limitCarrier.carrier,
                      (V : Set G.limitCarrier.carrier) = Q ∪ N.region a b →
                      (V : Set G.limitCarrier.carrier) ⊆ X →
                      ∃ B : ℝ, 0 < B ∧
                        intrinsicDiameter G.limitMetric (V : Set G.limitCarrier.carrier) ≤
                          ENNReal.ofReal B := by
  obtain ⟨epsilon0, hpos, hsmall, hbound⟩ :=
    exists_retained_positive_distance_bound_accuracy P
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.t2Space
  intro D0 L j hcenter hstage sigma hsigma f hf hheight hgraphs
    X hside N Q hQo hQX hQcl a b ha hb V hV hVX
  let D := (4 * standardSpherePathCeiling) * L.scale + 2 * W.radius
  have hP : 0 < standardSpherePathCeiling := standardSpherePathCeiling_pos
  have hscale : 0 < L.scale := L.scale_pos
  have hR : 0 < W.radius := W.radius_pos
  have hD : 0 < D := by dsimp [D]; positivity
  apply exists_intrinsicDiameter_bound_of_neck_recut N hQo
    (fun _ hx => (hQX hx).2) hQcl ha hb V hV G.base hD
  intro x hx
  exact hbound H W hepsilon G D0 L j hcenter hstage sigma hsigma f hf hheight hgraphs
    x (hside x (hVX hx))

end PoincareConjecture.M28.CounterexampleNeckFamily
