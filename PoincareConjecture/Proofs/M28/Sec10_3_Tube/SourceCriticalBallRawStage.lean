import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenInclusionDiffeomorph
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EmbeddingInverse









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}




noncomputable def regularRawStageDiffeomorph (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    PartialDiffeomorph (𝓡 3) (𝓡 3) G.limitCarrier.carrier
      ((E (phi (G.subsequence k) + H.shift)).flow.slice
        (E (phi (G.subsequence k) + H.shift)).time).carrier ∞ := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let i := phi (G.subsequence k)
  let e₁ := openSubtypePartialDiffeomorph (H.tubeCriticalRegion T A1 i)
    ⟨H.tubeCriticalBase T A1 hA1 i⟩
  let e₂ := openSubtypePartialDiffeomorph (T i).carrierOpen ⟨H.tubeBase T i⟩
  exact ((G.stageDiffeomorph k).trans e₁).trans e₂



@[simp] theorem regularRawStageDiffeomorph_source (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) (k : ℕ) :
    (H.regularRawStageDiffeomorph T A1 hA1 phi G k).source = G.exhaustion k := by
  change (G.exhaustion k ∩ (G.embedding k) ⁻¹' (univ : Set _) ∩
    (fun x => (G.embedding k x).val) ⁻¹' (univ : Set _)) = G.exhaustion k
  simp only [preimage_univ, inter_univ]



@[simp] theorem regularRawStageDiffeomorph_apply (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) (k : ℕ)
    (x : G.limitCarrier.carrier) :
    H.regularRawStageDiffeomorph T A1 hA1 phi G k x = (G.embedding k x).val.val := rfl

set_option maxHeartbeats 2400000 in



@[simp] theorem regularRawStageDiffeomorph_target (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) (k : ℕ) :
    (H.regularRawStageDiffeomorph T A1 hA1 phi G k).target =
      (fun x => (G.embedding k x).val.val) '' G.exhaustion k := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  rw [← (H.regularRawStageDiffeomorph T A1 hA1 phi G k).toPartialEquiv.image_source_eq_target]
  rw [H.regularRawStageDiffeomorph_source]
  rfl

set_option maxHeartbeats 2400000 in



@[simp] theorem regularRawStageDiffeomorph_base (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) (k : ℕ) :
    H.regularRawStageDiffeomorph T A1 hA1 phi G k G.base =
      (H.segment (phi (G.subsequence k))).path (H.segment (phi (G.subsequence k))).lower := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  rw [H.regularRawStageDiffeomorph_apply, G.base_preserving]
  rfl

end PoincareConjecture.M28.CounterexampleNeckFamily
