import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Path
import PoincareLib.Geometry.RicciFlow.Surgery.Global.Theory
import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.LocalTheory
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.Statement
import PoincareLib.Topology.Manifold.Surgery.Children.Statement

/-!
# M56 finite ancestry and component-cover statement

The conditional branch takes the actual M52 flow, connected initial slice,
trivial initial groups, and an event witness W. At every nonempty
event W already assumes trivial parent groups at all M54-selected survivor
basepoints and supplies simply connected children, with literal M38/M54/M55
provenance. The conditional branch does not construct W from those groups.
The Poincare branch constructs this witness from simple connectedness of the
original initial manifold. Both ancestry outputs choose one initial selected
component covering the connected initial slice, and every path starts there.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Natural-language conditional theorem: on an actual M52 flow with connected
initial slice and trivial initial groups, assume an event witness
whose parent groups at every M54-selected survivor basepoint of every nonempty
event are trivial, whose children are simply connected, and whose topology,
group and child data are the selected M38/M54/M55 outputs. Then finitely many
coherent component paths cover each time slice;
regular slabs transport a selected component and each surgery transition has
an inherited point in the interior retained region whose retention image lies
in the selected post-surgery component. Each path carries the M54 trivial-group
persistence certificate for its selected component function.

Source: blueprint `def:path-of-components` (`52c756bceff7`) and
`thm:component-fundamental-group-persistence` (`5f0941d364d0`) from
`extinction-and-component-topology.tex:8-29,549-579`, with
Morgan--Tian Definition 18.2 and its surgery continuation discussion
(`references/derived/MT2007.txt:20566-20596`), Claim 18.8
(`references/derived/MT2007.txt:20701-20715`), and Proposition 18.9's
component-path argument (`references/derived/MT2007.txt:20780-20805`).
The connected-sum and child-group inputs are Proposition 15.3 (printed
pp. 357-358; `references/derived/MT2007.txt:17814-17820`) and the M54/M55
adapters.  The changing-carrier `RepairedComponentPath` is the typed
per-slice adapter for the source's open spacetime path; regular slab
transport, terminal membership, and the event overlap witness supply its
coherence at this interface.  The correction record requires a retained-region
overlap/retention witness rather than whole-parent identifications
(`reviews/errata/2026-09-10-surgery-extinction-audit.md:42-47,132-137`).
-/
def RepairedLocalTopologyProviderRealization
    (G38 : RepairedLocalSurgeryTopologyTheory.{u})
    {g₀ : StandardInitialMetric}
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (N : NormalizedInitialMetric (M := M))
    (D : RepairedGlobalFlowData N)
    (F : RepairedSurgeryFlowData.{u} g₀)
    (hF : F.flow = D.certificate.flow)
    (W : RepairedEventChildWitness F.flow) : Prop :=
  ∃ A : RepairedNeckCapTopologyTheory.{u},
    let epsilon₀ := Classical.choose (G38.topology A)
    let hprovider := Classical.choose_spec (G38.topology A)
    ∃ hsmall : terminalAccuracyFactor * F.flow.parameters.epsilon ≤ epsilon₀,
      ∃ L : RepairedLocalSurgeryTopologyData F,
        L = Classical.choice
            (hprovider.2.2 F (by simpa [hF] using D.certificate.admissible) hsmall) ∧
          ∀ (T : ℝ) (hT : T ∈ F.flow.surgery_times)
            (hpost : Nonempty (F.flow.slice T).carrier),
            letI := hpost
            W.topology T hT hpost =
              (Classical.choice (L.nonempty_reconstruction T hT)).conclusion

/-- Retain the exact local group and child outputs used by the Poincare
induction. These are equalities of data, not equalities between proofs. -/
def M56PoincareProviderRealization
    (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    {F : SurgeryFlowData.{u}} {L : RawLocalSurgeryTopologyData F}
    (P : M56PoincareAncestryData F L) : Prop :=
  (∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier),
    letI := hpost
    P.witness.effects T hT hpost =
      Classical.choice (G54.effects (P.witness.topology T hT hpost))) ∧
  (∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier),
    letI := hpost
    ∀ hEffects : P.witness.effects T hT hpost =
        Classical.choice (G54.effects (P.witness.topology T hT hpost)),
      P.witness.children T hT hpost =
        Classical.choice (G55.components G54
          (P.witness.topology T hT hpost) (P.witness.effects T hT hpost)
          hEffects (P.witness.parent_groups_subsingleton T hT hpost)))

structure RepairedAncestryTheory : Prop where
  ancestry : ∀ (G38 : RepairedLocalSurgeryTopologyTheory.{u})
    (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M],
    ∀ (N : NormalizedInitialMetric (M := M))
      (D : RepairedGlobalFlowData N)
      {g₀' : StandardInitialMetric}
      (F : RepairedSurgeryFlowData.{u} g₀')
      (hF : F.flow = D.certificate.flow)
      (W : RepairedEventChildWitness F.flow),
      (initial_connected : IsConnected
        (Set.univ : Set (D.certificate.flow.slice 0).carrier)) →
      (initial_groups : ∀ x : (D.certificate.flow.slice 0).carrier,
        Subsingleton
          (FundamentalGroup (D.certificate.flow.slice 0).carrier x)) →
      RepairedLocalTopologyProviderRealization G38 N D F hF W →
      (∀ (T : ℝ) (hT : T ∈ F.flow.surgery_times)
        (hpost : Nonempty (F.flow.slice T).carrier),
        letI := hpost
        W.effects T hT hpost =
          Classical.choice (G54.effects (W.topology T hT hpost))) →
      (∀ (T : ℝ) (hT : T ∈ F.flow.surgery_times)
        (hpost : Nonempty (F.flow.slice T).carrier),
        letI := hpost
        ∀ hEffects : W.effects T hT hpost =
          Classical.choice (G54.effects (W.topology T hT hpost)),
        W.children T hT hpost =
          Classical.choice (G55.components G54
            (W.topology T hT hpost) (W.effects T hT hpost) hEffects
            (W.parent_groups_subsingleton T hT hpost))) →
      Nonempty (RepairedFiniteAncestryData D.certificate.flow (hF ▸ W))
  /-- From the simply connected initial manifold, construct the eventwise
  trivial-group witness and all ancestry on the supplied M52 flow. The local
  topology is the actual raw M38 output, fixed before this construction.
  Morgan--Tian Proposition 15.3, pp. 357--358, and Definition 18.2,
  pp. 419--420; the finite-history argument is Corollary 15.4, pp. 358--359. -/
  poincare : ∀ (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M],
    ∀ (N : NormalizedInitialMetric (M := M))
      (G : RepairedGlobalFlowData N)
      (L : RawLocalSurgeryTopologyData G.certificate.flow),
      Nonempty {P : M56PoincareAncestryData G.certificate.flow L //
        M56PoincareProviderRealization G54 G55 P}

end PoincareMT
