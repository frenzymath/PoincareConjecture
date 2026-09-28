import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Cap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.StrongNeck
import PoincareConjecture.Definitions.M27CanonicalGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaNormalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p x : M} {b epsilon C : ℝ}

def canonicalCapFromNormalization (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : M27CanonicalCap A.target 0 x epsilon C) : M27CanonicalCap K b x epsilon C where
  time_mem := hb
  cap := A.capFromNormalization N.cap
  epsilon_eq := by simpa only [capFromNormalization_epsilon] using N.epsilon_eq
  constant_le := by simpa only [capFromNormalization_cap_constant] using N.constant_le
  connection_eq := A.capFromNormalization_connection N.cap
  contains := by simpa only [capFromNormalization_core] using N.contains

def epsilonRoundComponentFromNormalization
    (A : AncientKappaNormalization K p b) (hb : b ≤ 0)
    (N : M27EpsilonRoundComponent A.target 0 epsilon) :
    M27EpsilonRoundComponent K b epsilon := by
  letI := N.reference_topology
  letI := N.reference_charted
  letI := N.reference_manifold
  refine { N with
    time_mem := hb
    scale := N.scale * A.scale
    scale_pos := mul_pos N.scale_pos A.scale_pos
    comparison := ?_ }
  have heq : m27RescaledPullbackMetric (K.flow.metric b) (N.scale * A.scale)
      N.identification = m27RescaledPullbackMetric (A.target.flow.metric 0)
        N.scale N.identification := by
    funext z a
    simp only [m27RescaledPullbackMetric, A.metric_eq, zero_div, add_zero]
    ring
  simpa only [heq] using N.comparison

end PoincareConjecture.AncientKappaNormalization
