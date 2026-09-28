import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Topology.ProjectiveProduct
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Topology.TwistedLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.StrongNeck











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace



def CoreNormalizedCurvatureTrichotomy : Prop :=
  ∀ (kappa : ℝ) (K : BasedKappaSolution kappa),
    (∀ t, t ≤ 0 → (K.flow.flow.connection t).StrictlyPositiveSectionalCurvature) ∨
      Nonempty (M27SphereLineFlowCertificate K.flow) ∨
      Nonempty (M27ProjectivePlaneLineFlowCertificate K.flow) ∨
      Nonempty (M27TwistedSphereLineFlowCertificate K.flow)



theorem M23TerminalExtension.positiveSectionalCurvature_of_pointSouls
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (T : M23TerminalExtension G)
    (hnoncompact : ∀ k, NoncompactSpace (S.term k).carrier.carrier)
    (hsoul : ∀ k, ∃ soul : RiemannianMetric.PointSoulData
      ((S.term k).flow.flow.metric 0), soul.center = (S.term k).base) :
    (G.limit.flow.flow.connection 0).StrictlyPositiveSectionalCurvature := by
  have hsoul' (k : ℕ) : Nonempty
      (RiemannianMetric.PointSoulData ((S.term k).flow.flow.metric 0)) := by
    obtain ⟨soul, _⟩ := hsoul k
    exact ⟨soul⟩
  rcases htrichotomy kappa G.limit with hpositive | hmodel | hprojective | htwisted
  · exact hpositive 0 le_rfl
  · obtain ⟨C⟩ := hmodel
    let delta := min neckSeparationThreshold (1 / 4) / 2
    have hmin : 0 < min neckSeparationThreshold (1 / 4) :=
      lt_min neckSeparationThreshold_pos (by norm_num)
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hsmall : delta < min neckSeparationThreshold (1 / 4) := by
      dsimp [delta]
      linarith
    have hhalf : delta < 1 / 2 := by
      have := min_le_right neckSeparationThreshold (1 / 4)
      linarith
    exact (T.not_strongEvolvingNeck_at_soul_limit hnoncompact hsoul hsmall
      (C.exists_strongEvolvingNeck le_rfl hdelta hhalf G.limit.base)).elim
  · exact (T.not_projectivePlaneLine_of_pointSouls hsoul' hprojective).elim
  · exact (T.not_twistedSphereLine_of_pointSouls hsoul' htwisted).elim

end PoincareConjecture
