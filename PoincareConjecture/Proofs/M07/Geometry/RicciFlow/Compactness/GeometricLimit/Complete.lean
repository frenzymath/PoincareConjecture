import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Assembly
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.LimitCarrier















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

variable {n : ℕ} {T' T : ℝ}

namespace PointedGeometricConvergenceCore



def boundaryEscape
    {S : PointedFlowSequence n T' T}
    {L : FlowCarrier n} {F : BasedFlow n T' T L} {φ : ℕ → ℕ}
    (_hφ : StrictMono φ) (C : PointedGeometricConvergenceCore S L F φ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
    ∀ x ∈ @frontier L.carrier L.topologicalSpace (C.exhaustion j),
      ENNReal.ofReal A ≤
        ((S.carrier (φ k)).metricEMetricSpace
          ((S.flow (φ k)).metricAt 0)).edist
            (S.flow (φ k)).base
            ((C.embedding k).toFun (0, x)).2


theorem metricComplete_zero_of_boundary_escape
    {S : PointedFlowSequence n T' T}
    {L : FlowCarrier.{0} n} {F : BasedFlow n T' T L} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (C : PointedGeometricConvergenceCore S L F φ)
    (hT : T' < 0 ∧ 0 < T)
    (hescape : C.boundaryEscape hφ) :
    (C.toGeometricLimit hφ).limitCarrier.metricComplete
      ((C.toGeometricLimit hφ).limitFlow.metricAt 0) := by
  let G := C.toGeometricLimit hφ
  apply G.metricComplete_zero_of_boundary_escape hT
  exact hescape

end PointedGeometricConvergenceCore



theorem pointedRicciFlowCompactness_of_boundary_escape
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    (G : PointedGeometricConvergence H.sequence)
    (hescape : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
    ∀ x ∈ @frontier G.limitCarrier.carrier G.limitCarrier.topologicalSpace
        (G.exhaustion j),
      ENNReal.ofReal A ≤
        ((H.sequence.carrier (G.subsequence k)).metricEMetricSpace
          ((H.sequence.flow (G.subsequence k)).metricAt 0)).edist
            (H.sequence.flow (G.subsequence k)).base
            ((G.embedding k).toFun (0, x)).2) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  exact pointedRicciFlowCompactness_of_geometric_limit G
    (G.metricComplete_zero_of_boundary_escape H.time_bounds hescape)





theorem pointedRicciFlowCompactness_of_boundary_escape_of_subsequence
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (G : PointedGeometricConvergence (H.subsequence φ hφ).sequence)
    (hescape : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      ∀ x ∈ @frontier G.limitCarrier.carrier G.limitCarrier.topologicalSpace
          (G.exhaustion j),
        ENNReal.ofReal A ≤
          (((H.subsequence φ hφ).sequence.carrier (G.subsequence k)).metricEMetricSpace
            (((H.subsequence φ hφ).sequence.flow (G.subsequence k)).metricAt 0)).edist
              ((H.subsequence φ hφ).sequence.flow (G.subsequence k)).base
              ((G.embedding k).toFun (0, x)).2) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  obtain ⟨C⟩ := pointedRicciFlowCompactness_of_boundary_escape
    (H := H.subsequence φ hφ) G hescape
  exact ⟨C.ofSubsequence⟩



theorem pointedRicciFlowCompactness_of_core_boundary_escape
    {H : PointedRicciFlowCompactnessHypotheses n T' T}
    {L : FlowCarrier.{0} n} {F : BasedFlow n T' T L} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (C : PointedGeometricConvergenceCore H.sequence L F φ)
    (hescape : C.boundaryEscape hφ) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  let G := C.toGeometricLimit hφ
  exact pointedRicciFlowCompactness_of_geometric_limit G
    (PointedGeometricConvergenceCore.metricComplete_zero_of_boundary_escape
      hφ C H.time_bounds hescape)

end PoincareConjecture
