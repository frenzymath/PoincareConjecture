import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.TransportTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Adapters
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Event.AncestryInput

/-!
# M57 local class transport proof entry

Natural-language theorem: on a raw surgery flow with raw M38 topology and
M56 Poincare ancestry, the M02 topology and M53 sphere-separation services
construct the actual M40 event inputs on each literal selected path. The
construction includes component metrics, separating neck spheres, the full
retained open region, integral third homology and point paths. Given those
inputs and one higher-basepoint service, the actual M40 comparison and M56
regular diffeomorphisms preserve each nonzero pi3 class. Finite chronological
composition and loop-space width construction belong to later milestones.
The conditional transport clause also applies independently to any supplied
M56 ancestry and coherent event inputs, without using the Poincare branch.

Source: Morgan--Tian Proposition 15.12 (printed p. 365;
`references/derived/MT2007.txt:18174-18193`), Definition 18.2
(`references/derived/MT2007.txt:20566-20596`), and the class-transport setup
before Proposition 18.18 (`references/derived/MT2007.txt:21081-21110`).
The specialization and exact coherence are required by the surgery-comparison
audit (`reviews/errata/2026-09-10-surgery-extinction-audit.md:42-47,132-137`).
The input construction, including the sphere-map and integral-homology
adapters, is derived in
`proof-work/tasks/M57/derivations/2026-09-25-event-input.md`.
The conditional transport proof retains the exact supplied comparison map.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Local homotopy-class transport on the literal ancestry components,
as in Proposition 15.12, p. 365, and the discussion before Proposition
18.18, pp. 430-431. -/
theorem repairedAncestryTransport : RepairedTransportTheory.{u} := by
  refine { poincare_inputs := ?_, transport := ?_ }
  · exact m57PoincareAncestryInput
  · intro B G40 g₀ D W A K C hC T hT x H
    exact m57AncestryTransport_of_input D W (A.path_for T hT x) K C H B

end PoincareMT
