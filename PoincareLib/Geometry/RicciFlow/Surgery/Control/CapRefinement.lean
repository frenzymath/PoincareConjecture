import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry

/-!
Adapted from Mapher `PoincareMT/Definitions/M45StandardGeometry.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
The standard-flow cap is expressed in the common Definition 9.72 certificate.
The +1 margin supplies its uniform strict bounds. Remark 9.73 permits reversing
the end-neck coordinate; the selected carrier, core and connection stay fixed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT

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

/-- The actual standard flow, with literal intrinsic cap or evolving-neck
geometry. The necks retain their exact time windows and the initial alternative
avoids the closed radius-`A0 + 4` cap in the initial standard metric. -/
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

end PoincareMT
