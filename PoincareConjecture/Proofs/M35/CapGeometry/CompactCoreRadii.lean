import PoincareConjecture.Proofs.M35.CapGeometry.LocalCoreRadius
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCoreRadius

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem blowupSequence_cap_core_curvature_balls_compact (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      ∀ K : Set L.limit.carrier.carrier, IsCompact K → K ⊆ N.core →
      ∀ᶠ k in atTop, ∀ y ∈ K,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        ∃ r : ℝ, 0 < r ∧
          scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
            (E.flow.connection (t (L.subsequence k)))
              ((E.flow.metric (t (L.subsequence k))).ball (f y) r) = r⁻¹ ^ 2 ∧
          closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r) ⊆ f '' N.carrier ∧
          IsCompact (closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N hconnection hcompact hU K hK hKN
  let good (k : ℕ) (y : L.limit.carrier.carrier) : Prop :=
    let f : L.limit.carrier.carrier → StandardCapSpace := fun z =>
      ((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
    ∃ r : ℝ, 0 < r ∧
      scalarCurvatureSupOn (E.flow.metric (t (L.subsequence k)))
        (E.flow.connection (t (L.subsequence k)))
          ((E.flow.metric (t (L.subsequence k))).ball (f y) r) = r⁻¹ ^ 2 ∧
      closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r) ⊆ f '' N.carrier ∧
      IsCompact (closure ((E.flow.metric (t (L.subsequence k))).ball (f y) r))
  have hlocal (y : K) : ∃ V : Set L.limit.carrier.carrier,
      IsOpen V ∧ y.1 ∈ V ∧ ∀ᶠ k in atTop, ∀ w ∈ V, good k w := by
    obtain ⟨V, hV, hyV, r, a, b, hr, hra, hab, z, hz, hcross, hgeometry⟩ :=
      N.exists_local_core_scalar_witness (hKN y.property)
    exact ⟨V, hV, hyV, blowupSequence_scalar_witness_curvature_balls
      P E t x ht hR L j N hconnection hcompact hU V r a b hr hra hab z hz hcross hgeometry⟩
  choose V hV hmem hgood using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV (fun y hy =>
    mem_iUnion.mpr ⟨⟨y, hy⟩, hmem ⟨y, hy⟩⟩)
  have hfinite : ∀ᶠ k in atTop, ∀ y ∈ s, ∀ w ∈ V y, good k w :=
    (eventually_all_finset s).mpr (fun y _ => hgood y)
  filter_upwards [hfinite] with k hk
  intro y hy
  obtain ⟨z, hz, hyV⟩ := mem_iUnion₂.mp (hs hy)
  exact hk z hz y hyV

end PoincareConjecture.M35.OrdinaryRealization
