import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage
import PoincareLib.Geometry.RicciFlow.Compactness.Assembly
import PoincareLib.Geometry.RicciFlow.Compactness.LimitCarrier

/-!
# Complete geometric limits from escaping boundaries

For a supplied pointed geometric convergence on a chosen exhaustion, boundary
escape gives source-ball coverage and a complete zero-time limit metric.
The two-time curvature bounds then give completeness at every interior time.
No completeness of an approximating source is used.

The geometric convergence and boundary escape remain hypotheses. Constructing
them from the frozen M07 assumptions requires controlled coordinates and a
compatible exhaustion. The core adapter below records the same assembly before
the frozen convergence record is packaged.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

variable {n : ℕ} {T' T : ℝ}

namespace PointedGeometricConvergenceCore

/-- The boundary-escape condition for the exhaustion retained by a local
geometric-limit core. -/
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

/-- Boundary escape makes the zero-time metric of the core limit complete. -/
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

/-- A pointed geometric convergence whose exhaustion boundaries escape every
fixed source ball satisfies the frozen compactness conclusion. -/
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

/-- Boundary escape on a strict reindexing gives the frozen conclusion for the
original sequence.  Geometric-limit construction naturally selects a
subsequence before the final contract is assembled; this adapter preserves
that selection while restoring the original hypothesis object. -/
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

/-- A chosen-exhaustion core together with boundary escape supplies the frozen
compactness conclusion. -/
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

end PoincareMT
