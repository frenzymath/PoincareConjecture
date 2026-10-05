import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Theory
import PoincareLib.Topology.Manifold.EmbeddedSphere.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Theory

/-!
# M57 local class transport statement

The Poincare branch constructs the primitive comparison inputs on the literal
M56 ancestry path from M02, M53 and raw local surgery topology. The conditional
transport output uses the actual M40 comparison provider on that path. Width
functionals and the pi2/pi3 loop-space bridge belong to M59 and later nodes.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

def RepairedComparisonProviderRealization
    (G40 : RepairedComparisonHomotopyTheory.{u})
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    {K : RepairedComparisonMapData D}
    (C : RepairedComparisonHomotopyData D K) : Prop :=
  ∃ P : RepairedClosedTopologyProvider.{u},
    ∃ G39 : RepairedComparisonMapTheory.{u},
      let epsilon₀ := Classical.choose (G40.homotopy P G39)
      let hprovider := Classical.choose_spec (G40.homotopy P G39)
      ∃ hsmall : terminalAccuracyFactor * D.flow.parameters.epsilon ≤ epsilon₀,
        ∃ hK : RepairedComparisonMapProviderRealization G39 D K,
          C = Classical.choice (hprovider.2 D hsmall K hK)

/-
Natural-language theorem: given an actual M40 comparison-homotopy provider,
one project-owned higher-basepoint transport service induced by explicit
`GenLoop` whiskering, each M56 changing-carrier path selected by the finite
ancestry data, and
explicit primitive coherence data selecting
the M40 parent and survivor child at each surgery time on that path, the M40
comparison conclusion is available and transports every specified nonzero
third homotopy class across the event.  On a surgery-free slab, the actual
M56 diffeomorphism transports every specified nonzero third class along its
explicitly supplied basepoint paths.  The M40 conclusion retains the
smooth approximants, degree/homotopy-equivalence, and metric estimate; this
milestone exposes that conclusion and its nonzero-class consequence.  It does
not assert a loop-space width or a pi2/pi3 identification.

Source: Morgan--Tian Proposition 15.12 (printed p. 365;
`references/derived/MT2007.txt:18174-18193`) for the separating-surgery map;
the path-of-components and class-transport paragraph preceding Proposition
18.18 (`references/derived/MT2007.txt:21081-21110`); and Definition 18.2
(`references/derived/MT2007.txt:20566-20596`).  The source assumes a fixed
nonzero class and pi2-trivial path, while this M40 specialization takes the
simple-connected parent/child and map conclusion as explicit primitive input.
The source warns that global homotopy/degree assertions need the additional
topology specialization; see
`reviews/errata/2026-09-10-surgery-extinction-audit.md:42-47,132-137` and
open issues `MT-SURGERY-COMPARISON`, `MT-TOPOLOGY-SPECIALIZATION`, and
`MT-EXTINCTION-JUMPS` in `reviews/redesign-errata.json`.  Finite chronological
composition of these local steps is owned by the later M69 finite-piece
propagation node.

In the Poincare branch, M02 topology and M53 sphere separation construct the
primitive event inputs for each literal path of an M56 Poincare ancestry on
the same raw flow and raw M38 topology. This includes the actual component
metric pullbacks, exact separating neck spheres, full retained open set,
parent integral third-homology identification and genuine point paths. No
comparison input, homology generator or extinction premise is supplied by
the caller. The source derivation and internal topological obligations are
in `reviews/contracts/2026-09-17-m57-poincare-inputs-round1.md`.
-/
structure RepairedTransportTheory : Prop where
  poincare_inputs :
    (P02 : RepairedClosedTopologyProvider.{u}) →
    (G53 : RepairedSphereSeparationTheory.{u}) →
    ∀ {g₀ : StandardInitialMetric}
      (D : RepairedSurgeryFlowData.{u} g₀)
      (L : RawLocalSurgeryTopologyData D.flow)
      (P : M56PoincareAncestryData D.flow L)
      (K : RepairedComparisonMapData D)
      (C : RepairedComparisonHomotopyData D K)
      (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      Nonempty (RepairedAncestryTransportInput D P.witness
        (P.ancestry.path_for T hT x) K C)
  transport : ∀ (B : M59HigherBasepointTransportService.{u}),
    ∀ (G40 : RepairedComparisonHomotopyTheory.{u}),
    ∀ {g₀ : StandardInitialMetric}
      (D : RepairedSurgeryFlowData.{u} g₀)
      (W : RepairedEventChildWitness D.flow)
      (A : RepairedFiniteAncestryData D.flow W)
      {K : RepairedComparisonMapData D}
      (C : RepairedComparisonHomotopyData D K),
      RepairedComparisonProviderRealization G40 D C →
      ∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
        (x : (D.flow.slice T).carrier),
        (H : RepairedAncestryTransportInput D W
          (A.path_for T hT x) K C) →
        Nonempty (RepairedAncestryTransportData D W
          (A.path_for T hT x) K C H B)

end PoincareMT
