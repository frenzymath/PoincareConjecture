import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.ProjectivePlaneLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.ProjectivePlane
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Nonorientable










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Poincare.Topology.Orientation.ProjectivePlane

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



theorem RiemannianMetric.PointSoulData.noEmbeddedTrivialNormalProjectivePlane
    {g : RiemannianMetric 3 M} (P : RiemannianMetric.PointSoulData g)
    (K : AncientKappaSolution 3 M) :
    NoEmbeddedTrivialNormalProjectivePlane K := by
  rintro ⟨f, hf⟩
  let F : RealProjectiveTwo × NormalInterval → E3 :=
    P.euclidean.symm ∘ f
  have hF : Topology.IsOpenEmbedding F :=
    P.euclidean.symm.toHomeomorph.isOpenEmbedding.comp hf
  let : T2Space (RealProjectiveTwo × NormalInterval) := hF.isEmbedding.t2Space
  let : LocallyCompactSpace (RealProjectiveTwo × NormalInterval) :=
    hF.locallyCompactSpace
  exact projectivePlaneThickening_not_orientable
    (euclideanLocalOrientation.pullback ⟨F, hF.continuous⟩ hF)

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace



theorem M23TerminalExtension.noEmbeddedTrivialNormalProjectivePlane_of_pointSouls
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hsoul : ∀ k, Nonempty
      (RiemannianMetric.PointSoulData ((S.term k).flow.flow.metric 0))) :
    NoEmbeddedTrivialNormalProjectivePlane G.limit.flow := by
  apply T.noEmbeddedTrivialNormalProjectivePlane
  intro k
  obtain ⟨P⟩ := hsoul k
  exact P.noEmbeddedTrivialNormalProjectivePlane (S.term k).flow



theorem M23TerminalExtension.not_projectivePlaneLine_of_pointSouls
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hsoul : ∀ k, Nonempty
      (RiemannianMetric.PointSoulData ((S.term k).flow.flow.metric 0))) :
    ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate G.limit.flow) :=
  (T.noEmbeddedTrivialNormalProjectivePlane_of_pointSouls hsoul).not_projectivePlaneLine

end PoincareConjecture
