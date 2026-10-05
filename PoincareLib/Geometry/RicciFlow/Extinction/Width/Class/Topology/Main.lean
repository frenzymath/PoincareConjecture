import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Topology.Providers
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Basepoint.Service
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.IdentificationSystem

/-!
# M59 loop classes and basepoint transport proof entry

The coherent loop-space identification uses C1 approximation, cubical
adjunction and the compact and noncompact universal-cover arguments.
The higher-basepoint service is constructed from cubical homotopy extension.
Component realization and M58's short-loop consequence are checked
applications of that construction.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- M59: given the applied M02 closed-topology and M58 short-loop services,
construct one coherent C1-loop-space comparison system. On every closed
connected smooth three-manifold with pi2=0 and a chosen point, it identifies
pi2 of the null-loop component with pi3 of the manifold, relates the genuine
absolute and relative square models, and supplies normalized regular sphere
representatives. Raw free homotopy characterizes their based class equality
and yields regular-family homotopy. Smooth maps give actual regular
postcomposition and commute with the same chosen comparisons.

For the free-class comparison, use the simply connected cover: on a compact
cover apply M02 and the degree/Lefschetz argument for the deck action; on a
noncompact cover use Hurewicz and top-dimensional homology vanishing. The
general finite-free-product classification, finite-cover package and full
noncompact contractibility are not exported by this milestone.

On a selected surgery component, realize a specified pi3 class using the
same sphere parameter and comparison. Under M58's uniform short-loop length
threshold on the chosen metric, this represented class is the identity.
The legacy width adapter retains its actual carrier, metric and class.

Also construct one higher-homotopy basepoint service on every space in the
working universe. Its maps descend from actual GenLoop operations, satisfy
identity, path-composition and reverse-path laws, preserve the group identity
and multiplication in positive dimensions, and commute with continuous
postcomposition. Homotopy extension gives the positive-dimensional operation
equivalent to Hatcher's beta_(p.symm) for a path p from source to target;
at dimension zero it preserves the path-component class. These are
construction methods for the exported laws, not additional defining
equations in the service type.

Sources: Morgan--Tian Claim 18.16 and Definition 18.17, p. 430; Lemma 18.27 and
Corollary 18.28, p. 434. Perelman III Section 1 supplies the relative-loop
formulation. The fixed-point/free-class argument uses Hatcher Theorem 2C.3,
p. 179, and Proposition 4A.2, p. 422, with the archived corrections. The
full derivation, homology support, corrected short-loop threshold and C1
qualification are in `reviews/contracts/M59-round1.md`, as narrowed by
`reviews/contracts/2026-09-20-note05-contract-amendments.md`, and
`reviews/errata/2026-09-10-surgery-extinction-audit.md`. The 2015 Section 19.2
correction does not change these Chapter 18 topology claims. Basepoint
transport uses Hatcher Section 4.1, pp. 341-342; its derivation and producer
ownership are in `reviews/contracts/2026-09-17-m59-basepoint-producer-round1.md`. -/
theorem m59LoopClassesAndComponentTopology
    (P02 : RepairedClosedTopologyProvider.{u})
    (P58 : RepairedShortLoopTrivialityTheory.{u}) :
    M59LoopClassesAndComponentTopologyTheory.{u} := by
  let S := m59IdentificationSystem P02
  refine ⟨S, m59ComponentRepresentative_from_identification S, ?_⟩
  exact ⟨m59ShortLoopPiThree_of_service P58 S, m59HigherBasepointTransportService_nonempty⟩

/-- Apply the exact earlier milestones once for downstream consumers. -/
theorem m59LoopClassesAndComponentTopology_from_predecessors :
    M59LoopClassesAndComponentTopologyTheory.{u} :=
  m59LoopClassesAndComponentTopology m59ClosedTopologyProvider_from_M02
    repairedShortLoopTriviality

end PoincareMT
