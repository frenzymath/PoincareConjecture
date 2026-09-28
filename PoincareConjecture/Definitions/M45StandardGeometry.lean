import PoincareConjecture.Definitions.Ch12.StandardCap







set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

structure M45StandardCapRefinement {A : StandardCylinderAtlas}
    {g₀ : StandardInitialMetric} {F : MaximalStandardCapFlow g₀}
    {t gamma C : ℝ} {x : StandardCapSpace}
    (N : StandardCapNeighborhood A F t gamma C x) where
  cap : CapCertificate (F.metric t)
  epsilon_eq : cap.epsilon = gamma
  constant_eq : cap.cap_constant = C + 1
  connection_eq : cap.connection = F.connection t
  carrier_eq : cap.carrier = N.carrier
  closed_core_eq : cap.closed_core = N.closed_core
  model_eq : cap.model_kind = .euclidean
  contains : x ∈ cap.core




inductive M45StandardCanonicalAlternative (A : StandardCylinderAtlas)
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    (t : ℝ) (x : StandardCapSpace) (gamma C : ℝ) : Prop
  | cap (N : CapCertificate (F.metric t))
      (epsilon_eq : N.epsilon = gamma)
      (constant_le : N.cap_constant ≤ C)
      (connection_eq : N.connection = F.connection t)
      (model_eq : N.model_kind = .euclidean)
      (contains : x ∈ N.core)
  | initial_neck
      (N : StandardEvolvingNeck A F t gamma x
        (Set.Icc (-t * (F.connection t).scalarCurvature x) 0))
      (initial_disjoint : Disjoint N.patch.carrier
        {y | g₀.metric.edist 0 y ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 4)})
  | evolving_neck
      (N : StandardEvolvingNeck A F t gamma x (Set.Ioc (-(1 + gamma)) 0))

end PoincareConjecture
