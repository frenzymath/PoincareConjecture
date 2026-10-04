import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenInclusionDiffeomorph
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Ends.SourceTubeCriticalRegion
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.EmbeddingInverse

/-!
# The actual regular-stage map into the original raw slice

Compose the original regular embedding with both literal open inclusions.
Its guarded inverse has exactly the raw image as domain. Source:
Morgan--Tian Proposition 10.7, p. 253; M28 derivation 102.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

/-- The raw partial diffeomorphism retains both actual inclusions and the
literal composite source index. It makes no metric-isometry assertion.
Source: Proposition 10.7, p. 253; M28 derivation 102. -/
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

/-- Both inclusion domains are full, so the raw source is exactly the
original regular stage. Source: M28 derivation 102. -/
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

/-- Forward evaluation is the original embedding followed by its two
literal subtype values. Source: M28 derivation 102. -/
@[simp] theorem regularRawStageDiffeomorph_apply (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) (k : ℕ)
    (x : G.limitCarrier.carrier) :
    H.regularRawStageDiffeomorph T A1 hA1 phi G k x = (G.embedding k x).val.val := rfl

set_option maxHeartbeats 2400000 in
-- Reducing the image through both dependent open inclusions exceeds the default budget.
/-- The inverse is guarded by the exact raw image of the regular stage.
Source: Proposition 10.7, p. 253; M28 derivation 102. -/
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
-- The dependent composite source index requires extra reduction to expose its base readout.
/-- The raw-stage map sends the retained limit base to the literal low
endpoint in the original slice. Source: Proposition 10.7; derivation 102. -/
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

end PoincareMT.M28.CounterexampleNeckFamily
