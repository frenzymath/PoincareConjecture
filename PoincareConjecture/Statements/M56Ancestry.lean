import PoincareConjecture.Definitions.M56Ancestry
import PoincareConjecture.Statements.M52GlobalFlow
import PoincareConjecture.Statements.M38LocalTopology
import PoincareConjecture.Statements.M54GroupEffects
import PoincareConjecture.Statements.M55ChildComponents

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

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
    ∃ hsmall : 2 * F.flow.parameters.epsilon ≤ epsilon₀,
      ∃ L : RepairedLocalSurgeryTopologyData F,
        L = Classical.choice
            (hprovider.2.2 F (by simpa [hF] using D.certificate.admissible) hsmall) ∧
          ∀ (T : ℝ) (hT : T ∈ F.flow.surgery_times)
            (hpost : Nonempty (F.flow.slice T).carrier),
            letI := hpost
            W.topology T hT hpost =
              (Classical.choice (L.nonempty_reconstruction T hT)).conclusion

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

end PoincareConjecture
