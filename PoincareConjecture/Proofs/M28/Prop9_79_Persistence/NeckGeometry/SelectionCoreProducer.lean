import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.SourceNeckPullback
import PoincareConjecture.Proofs.M28.Generalized.QuantitativeBackwardWindow

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.NeckGeometry

open PoincareConjecture.Proofs.M28.NeckTransfer

theorem PartialLimitWindowExport.exists_target_core_of_singular_neck_tube
    {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {tau : ℝ}
    {F : ∀ k, RicciFlow 3 (M k) (Icc (-tau) 0)}
    {p : ∀ k, M k} {A epsilon : ℝ}
    (E : PartialLimitWindowExport F p A)
    (D : letI := E.limit.limitCarrier.topologicalSpace
      letI := E.limit.limitCarrier.chartedSpace
      letI := E.limit.limitCarrier.isManifold
      LeviCivitaData E.limit.limitMetric)
    (T : letI := E.limit.limitCarrier.topologicalSpace
      letI := E.limit.limitCarrier.measurableSpace
      letI := E.limit.limitCarrier.borelSpace
      letI := E.limit.limitCarrier.chartedSpace
      letI := E.limit.limitCarrier.isManifold
      letI := E.limit.limitCarrier.t2Space
      letI := E.limit.limitCarrier.t3Space
      SingularNeckTube E.limit.limitMetric D epsilon)
    (j : ℕ)
    (N : EpsilonNeck ((F (E.limit.subsequence j)).metric 0))
    (hcapture : N.carrier ⊆
      E.limit.embedding j '' E.limit.exhaustion j)
    (hcenter : N.center = p (E.limit.subsequence j))
    (hpoint : letI := E.limit.limitCarrier.topologicalSpace
      letI := E.limit.limitCarrier.measurableSpace
      letI := E.limit.limitCarrier.borelSpace
      letI := E.limit.limitCarrier.chartedSpace
      letI := E.limit.limitCarrier.isManifold
      letI := E.limit.limitCarrier.t2Space
      letI := E.limit.limitCarrier.t3Space
      stageInverse E.limit.toPartialPointedMetricConvergence j N.center ∈
        T.carrier)
    (hscale : letI := E.limit.limitCarrier.topologicalSpace
      letI := E.limit.limitCarrier.chartedSpace
      letI := E.limit.limitCarrier.isManifold
      N.scale = D.scalarCurvature
        (stageInverse E.limit.toPartialPointedMetricConvergence j N.center) ^
          (-1 / 2 : ℝ)) :
    letI := E.limit.limitCarrier.topologicalSpace
    letI := E.limit.limitCarrier.chartedSpace
    letI := E.limit.limitCarrier.isManifold
    ∃ C : NeckGeometryCore E.limit.limitMetric N.epsilon,
      C.center = E.limit.base := by
  classical
  letI := E.limit.limitCarrier.topologicalSpace
  letI := E.limit.limitCarrier.measurableSpace
  letI := E.limit.limitCarrier.borelSpace
  letI := E.limit.limitCarrier.chartedSpace
  letI := E.limit.limitCarrier.isManifold
  letI := E.limit.limitCarrier.t2Space
  letI := E.limit.limitCarrier.t3Space
  have hscalar : 0 < D.scalarCurvature
      (stageInverse E.limit.toPartialPointedMetricConvergence j N.center) := by
    have hlow := T.scalar_lower
      (stageInverse E.limit.toPartialPointedMetricConvergence j N.center) hpoint
    linarith
  let C := captured_source_neck_geometry_of_window E j N hcapture
    D hscalar hscale
  refine ⟨C, ?_⟩
  change stageInverse E.limit.toPartialPointedMetricConvergence j N.center =
    E.limit.base
  rw [hcenter, ← E.limit.base_preserving j]
  let G := E.limit.toPartialPointedMetricConvergence
  let U := G.exhaustion j
  let f : U → M (G.subsequence j) := fun x => G.embedding j x
  letI : Nonempty U := ⟨G.base, G.base_in_exhaustion j⟩
  dsimp [stageInverse, G, U, f]
  exact congrArg Subtype.val
    (Function.leftInverse_invFun (G.embedding_open j).injective
      ⟨G.base, G.base_in_exhaustion j⟩)

end PoincareConjecture.M28.NeckGeometry
