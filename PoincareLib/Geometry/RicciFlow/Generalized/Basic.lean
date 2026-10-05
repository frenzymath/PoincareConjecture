import PoincareLib.Geometry.RicciFlow.Basic

/-!
# Generalized Ricci flows and their time slices

Adapted from Mapher, `PoincareMT/Definitions/Ch11/BlowupLimits.lean`, commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Declaration bodies are retained; only the required definition closure is imported.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

structure GeneralizedSliceCarrier where
  carrier : Type u
  topologicalSpace : TopologicalSpace carrier
  measurableSpace : MeasurableSpace carrier
  borelSpace : @BorelSpace carrier topologicalSpace measurableSpace
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier
  isManifold : IsManifold (𝓡 3) ∞ carrier
  t2Space : T2Space carrier
  t3Space : T3Space carrier
  secondCountable : SecondCountableTopology carrier

attribute [instance] GeneralizedSliceCarrier.topologicalSpace
  GeneralizedSliceCarrier.measurableSpace GeneralizedSliceCarrier.borelSpace
  GeneralizedSliceCarrier.chartedSpace GeneralizedSliceCarrier.isManifold
  GeneralizedSliceCarrier.t2Space GeneralizedSliceCarrier.t3Space
  GeneralizedSliceCarrier.secondCountable

structure GeneralizedRicciFlowBox
    (S : ℝ → GeneralizedSliceCarrier.{u})
    (g : ∀ t : ℝ, RiemannianMetric 3 (S t).carrier) (J : Set ℝ) where
  carrier : GeneralizedSliceCarrier.{u}
  interval : Set ℝ
  relatively_open : ∃ U : Set ℝ, IsOpen U ∧ interval = J ∩ U
  flow : RicciFlow 3 carrier.carrier interval
  forward : ∀ t : ℝ, t ∈ interval → carrier.carrier → (S t).carrier
  inverse : ∀ t : ℝ, t ∈ interval → (S t).carrier → carrier.carrier
  forward_openEmbedding : ∀ t ht, Topology.IsOpenEmbedding (forward t ht)
  forward_smooth : ∀ t ht, ContMDiff (𝓡 3) (𝓡 3) ∞ (forward t ht)
  inverse_smooth : ∀ t ht,
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inverse t ht) (Set.range (forward t ht))
  left_inverse : ∀ t ht, Function.LeftInverse (inverse t ht) (forward t ht)
  right_inverse : ∀ t ht,
    Set.LeftInvOn (forward t ht) (inverse t ht) (Set.range (forward t ht))
  metric_pullback : ∀ t ht x u v,
    (g t).inner (forward t ht x)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x u)
      (mfderiv (𝓡 3) (𝓡 3) (forward t ht) x v) =
      (flow.metric t).inner x u v

structure GeneralizedRicciFlowData where
  slice : ℝ → GeneralizedSliceCarrier.{u}
  interval : Set ℝ
  interval_connected : interval.OrdConnected
  interval_nontrivial : interval.Nontrivial
  slice_nonempty_iff : ∀ t, Nonempty (slice t).carrier ↔ t ∈ interval
  metric : ∀ t : ℝ, RiemannianMetric 3 (slice t).carrier
  connection : ∀ t : ℝ, LeviCivitaData (metric t)
  space_topology : TopologicalSpace (Σ t : ℝ, (slice t).carrier)
  space_t2 : @T2Space (Σ t : ℝ, (slice t).carrier) space_topology
  space_secondCountable :
    @SecondCountableTopology (Σ t : ℝ, (slice t).carrier) space_topology
  time_continuous : @Continuous (Σ t : ℝ, (slice t).carrier) ℝ
    space_topology inferInstance Sigma.fst
  slice_embedding : ∀ t,
    letI := space_topology
    Topology.IsEmbedding (fun x : (slice t).carrier ↦
      (⟨t, x⟩ : Σ s : ℝ, (slice s).carrier))
  box_index : Type u
  box : box_index → GeneralizedRicciFlowBox slice metric interval
  box_openEmbedding : ∀ b,
    letI := space_topology
    Topology.IsOpenEmbedding (fun p : (box b).interval × (box b).carrier.carrier ↦
      (⟨p.1.1, (box b).forward p.1.1 p.1.2 p.2⟩ : Σ t : ℝ, (slice t).carrier))
  box_covers : ∀ t (x : (slice t).carrier),
    ∃ b, ∃ ht : t ∈ (box b).interval, ∃ y, (box b).forward t ht y = x
  vertical_compatibility : ∀ b c t ht hc x y,
    (box b).forward t ht x = (box c).forward t hc y →
    ∀ s hs hs', (box b).forward s hs x = (box c).forward s hs' y

abbrev GeneralizedRicciFlowData.point (F : GeneralizedRicciFlowData) :=
  Σ t : ℝ, (F.slice t).carrier

instance GeneralizedRicciFlowData.pointTopology (F : GeneralizedRicciFlowData) :
    TopologicalSpace F.point := F.space_topology

noncomputable def GeneralizedRicciFlowData.scalar
    (F : GeneralizedRicciFlowData) (p : F.point) : ℝ :=
  (F.connection p.1).scalarCurvature p.2

end PoincareMT

