import PoincareLib.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic

/-!
# Compact subsets of an ancient convergence exhaustion

The increasing open exhaustion retained by ancient compact-time convergence
contains every compact subset in one stage.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.AncientCompactTimeConvergence

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

/-- Every compact subset of the limit lies in a single exhaustion stage. -/
theorem exists_exhaustion_superset (G : AncientCompactTimeConvergence S)
    {A : Set G.limit.carrier.carrier}
    (hA : @IsCompact G.limit.carrier.carrier G.limit.carrier.topologicalSpace A) :
    ∃ j, A ⊆ G.exhaustion j := by
  let : TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  exact hA.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) hmono.directed_le

end PoincareMT.AncientCompactTimeConvergence
