import PoincareConjecture.Proofs.M47.PositiveHistoryRegular
import PoincareConjecture.Proofs.M47.TerminalComponents

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem regular_pre_component_limit_image
    (E : SurgeryEventData g₀ K P slice metric T) (x : (slice E.tMinus).carrier)
    (hcompact : IsCompact (connectedComponent x))
    (hregular : connectedComponent x ⊆ E.regular_limit) :
    E.limit_identify.map '' connectedComponent x =
      connectedComponent (E.limit_identify.map x) := by
  let : LocallyConnectedSpace (slice E.tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  have hset : E.limit_identify.map '' connectedComponent x =
      E.limit_identify.inverse ⁻¹' connectedComponent x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [mem_preimage, E.limit_identify.left_inverse (hregular hz)] using hz
    · intro hy
      exact ⟨E.limit_identify.inverse y, hy, E.limit_identify.right_inverse (mem_univ y)⟩
  have hopen : IsOpen (E.limit_identify.map '' connectedComponent x) := by
    rw [hset]
    exact isOpen_connectedComponent.preimage
      (continuousOn_univ.mp E.limit_identify.inverse_smooth.continuousOn)
  have hcont := E.limit_identify.map_smooth.continuousOn.mono hregular
  have hcomp := hcompact.image_of_continuousOn hcont
  have hconn := (isConnected_connectedComponent (x := x)).image E.limit_identify.map hcont
  have hx : E.limit_identify.map x ∈ E.limit_identify.map '' connectedComponent x :=
    ⟨x, mem_connectedComponent, rfl⟩
  exact Subset.antisymm (hconn.subset_connectedComponent hx)
    ((show IsClopen _ from ⟨hcomp.isClosed, hopen⟩).connectedComponent_subset hx)

theorem retained_regular_component_meets_core
    (E : SurgeryEventData g₀ K P slice metric T) (policy : SurgeryEventTerminalPolicy E)
    (x : (slice E.tMinus).carrier)
    (hcompact : IsCompact (connectedComponent x))
    (hregular : connectedComponent x ⊆ E.regular_limit)
    {q : (slice E.tMinus).carrier} (hq : q ∈ connectedComponent x)
    (hretained : q ∈ E.retained_pre) :
    ∃ y ∈ connectedComponent (E.limit_identify.map x),
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2 := by
  have hqterm : E.limit_identify.map q ∈ connectedComponent (E.limit_identify.map x) :=
    (regular_pre_component_limit_image E x hcompact hregular).subset ⟨q, hq, rfl⟩
  have hqret : E.limit_identify.map q ∈ E.limit_identify.map '' E.retained_pre :=
    ⟨q, hretained, rfl⟩
  rw [policy.retained_eq] at hqret
  obtain ⟨y, hyR, hqy⟩ := hqret.1
  have heq : connectedComponent y = connectedComponent (E.limit_identify.map x) :=
    (connectedComponent_eq hqy).trans (connectedComponent_eq hqterm).symm
  exact ⟨y, heq ▸ mem_connectedComponent, hyR⟩

theorem positive_pre_component_whole_retention
    (hC : RicciFlowCurvatureTheory.{u})
    (E : SurgeryEventData g₀ K P slice metric T) (policy : SurgeryEventTerminalPolicy E)
    [CompactSpace (slice E.tMinus).carrier]
    (v : Ico E.tMinus T) (x : (slice E.tMinus).carrier)
    (hpos : ∀ y ∈ connectedComponent x, ∀ u w : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (E.pre_flow.metric v.1) y u w →
        0 < (E.pre_flow.connection v.1).sectionalCurvature y u w)
    {q : (slice E.tMinus).carrier} (hq : q ∈ connectedComponent x)
    (hretained : q ∈ E.retained_pre) :
    connectedComponent x ⊆ interior E.retained_pre ∧
      E.retention.map '' connectedComponent x = connectedComponent (E.retention.map x) ∧
      ∀ i, Disjoint (E.retention.map '' connectedComponent x) (E.caps i).carrier := by
  have hregular := positive_component_subset_regular hC E v x hpos hq
    (E.retained_pre_subset hretained)
  have hcompact : IsCompact (connectedComponent x) := isClosed_connectedComponent.isCompact
  have hcompactT : IsCompact (connectedComponent (E.limit_identify.map x)) := by
    rw [← regular_pre_component_limit_image E x hcompact hregular]
    exact hcompact.image_of_continuousOn (E.limit_identify.map_smooth.continuousOn.mono hregular)
  have hlow := retained_regular_component_meets_core E policy x hcompact hregular hq hretained
  have hinv : E.limit_identify.inverse (E.limit_identify.map x) = x :=
    E.limit_identify.left_inverse (hregular mem_connectedComponent)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hinv] using policy.compact_pre_component_subset_interior hcompactT hlow
  · simpa only [hinv] using policy.compact_retention_image_component hcompactT hlow
  · intro i
    simpa only [hinv] using policy.compact_retention_image_disjoint_cap hcompactT hlow i

end PoincareConjecture.M47Positive
