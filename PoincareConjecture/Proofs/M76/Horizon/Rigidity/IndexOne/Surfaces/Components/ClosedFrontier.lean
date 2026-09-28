import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.SeparatedComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceCollarCoordinates
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem source_component_eq_frontier_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (phi : C(H, H)) (theta theta' : C)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (Hmodel : K.space ≃ₜ sourceSurface phi theta)
    {N S : Set X} (hN : IsClosed N)
    (hfront : frontier N = (N ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hS : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hrim : Disjoint S (frontier R)) :
    ∀ x ∈ S, connectedComponentIn (frontier N) x = S := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let : LocallyPathConnectedSpace K.space := K.locallyPathConnectedSpace_of_finite hK
  let : LocallyPathConnectedSpace (sourceSurface phi theta) :=
    Hmodel.isQuotientMap.locallyPathConnectedSpace
  let G := (N ∩ frontier R) ∪ sourceSurface phi theta'
  have hG : IsClosed G :=
    (hN.inter isClosed_frontier).union (sourceSurface_isCompact phi theta').isClosed
  have hsplit : frontier N = sourceSurface phi theta ∪ G := by
    rw [hfront]
    ext y
    simp only [G, mem_union]
    tauto
  intro x hx
  rw [hsplit]
  have hdis : Disjoint (connectedComponentIn (sourceSurface phi theta) x) G := by
    rw [hcomponent x hx]
    apply disjoint_left.mpr
    intro y hy hyG
    rcases hyG with hyold | hyother
    · exact disjoint_left.mp hrim hy hyold.2
    · exact disjoint_left.mp hAB (hS hy) hyother
  rw [connectedComponentIn_union_eq_of_disjoint
    (sourceSurface_isCompact phi theta).isClosed hG (hS hx) hdis, hcomponent x hx]

end PoincareConjecture.M76.HamiltonIntervalTorus
