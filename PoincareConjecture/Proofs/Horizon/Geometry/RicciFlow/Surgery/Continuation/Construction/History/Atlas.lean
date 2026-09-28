import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Events.Boxes
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas.CountableCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Atlas.Topology

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)

def ordinaryCover : Set (OrdinaryTimeWindow W) :=
  Classical.choose (exists_countable_ordinary_boxes W)

theorem ordinaryCover_countable : (ordinaryCover W).Countable :=
  (Classical.choose_spec (exists_countable_ordinary_boxes W)).1

def eventWindow (e : ↥(F.surgery_times ∩ W.interval)) : EventTimeWindow W e.property.1 e.property.2 :=
  Classical.choice (exists_eventTimeWindow W e.property.1 e.property.2)

abbrev BoxIndex := ULift.{u} (ordinaryCover W) ⊕ ULift.{u} ↥(F.surgery_times ∩ W.interval)

instance : Countable (BoxIndex W) := by
  have : Countable (ordinaryCover W) := (ordinaryCover_countable W).to_subtype
  have : Countable ↥(F.surgery_times ∩ W.interval) := W.events_finite.countable.to_subtype
  infer_instance

variable (L : ∀ t, t ∈ F.surgery_times → t ∈ W.interval →
  RicciFlowLocalTheory 3 (F.slice t).carrier)

def atlasBox : BoxIndex W → GeneralizedRicciFlowBox (slice W) (metric W) W.interval
  | Sum.inl a => a.down.val.box
  | Sum.inr e =>
      letI := W.slice_nonempty e.down.val e.down.property.2
      (eventWindow W e.down).box (L e.down.val e.down.property.1 e.down.property.2)

theorem atlasBox_slab_compatibility (i : BoxIndex W) : SlabCompatible (atlasBox W L i) := by
  cases i with
  | inl a => exact a.down.val.slab_compatibility
  | inr e =>
    let := W.slice_nonempty e.down.val e.down.property.2
    exact (eventWindow W e.down).box_slab_compatibility _

theorem distinct_atlasBoxes_regular_overlap (i j : BoxIndex W) (hne : i ≠ j) :
    Disjoint F.surgery_times ((atlasBox W L i).interval ∩ (atlasBox W L j).interval) := by
  apply disjoint_left.mpr
  intro t ht htI
  cases i with
  | inl a => exact a.down.val.regular htI.1 ht
  | inr e =>
    cases j with
    | inl a => exact a.down.val.regular htI.2 ht
    | inr f =>
      let := W.slice_nonempty e.down.val e.down.property.2
      let := W.slice_nonempty f.down.val f.down.property.2
      have he := (eventWindow W e.down).box_events_unique
        (L _ e.down.property.1 e.down.property.2) htI.1 ht
      have hf := (eventWindow W f.down).box_events_unique
        (L _ f.down.property.1 f.down.property.2) htI.2 ht
      apply hne
      exact congrArg Sum.inr (ULift.ext _ _ (Subtype.ext (he.symm.trans hf)))

theorem atlasBox_vertical_compatibility (i j : BoxIndex W)
    (t : ℝ) (hti : t ∈ (atlasBox W L i).interval) (htj : t ∈ (atlasBox W L j).interval)
    (x : (atlasBox W L i).carrier.carrier) (y : (atlasBox W L j).carrier.carrier)
    (hxy : (atlasBox W L i).forward t hti x = (atlasBox W L j).forward t htj y)
    (s : ℝ) (hsi : s ∈ (atlasBox W L i).interval) (hsj : s ∈ (atlasBox W L j).interval) :
    (atlasBox W L i).forward s hsi x = (atlasBox W L j).forward s hsj y := by
  classical
  by_cases hij : i = j
  · subst j
    have he : x = y := ((atlasBox W L i).forward_openEmbedding t hti).injective hxy
    exact congrArg ((atlasBox W L i).forward s hsi) he
  · exact boxes_vertical_of_regular_overlap _ _
      (atlasBox_slab_compatibility W L i) (atlasBox_slab_compatibility W L j)
      (distinct_atlasBoxes_regular_overlap W L i j hij) t hti htj x y hxy s hsi hsj

theorem atlasBox_covers (t : ℝ) (x : (slice W t).carrier) :
    ∃ i, ∃ ht : t ∈ (atlasBox W L i).interval,
      ∃ y, (atlasBox W L i).forward t ht y = x := by
  classical
  have htW : t ∈ W.interval := x.property.1
  by_cases htS : t ∈ F.surgery_times
  · let e : ↥(F.surgery_times ∩ W.interval) := ⟨t, htS, htW⟩
    let := W.slice_nonempty t htW
    obtain ⟨y, hy⟩ := (eventWindow W e).box_event_surjective (L t htS htW) x
    exact ⟨Sum.inr ⟨e⟩, (eventWindow W e).time_mem, y, hy⟩
  · obtain ⟨a, ha, ht, y, hy⟩ :=
      (Classical.choose_spec (exists_countable_ordinary_boxes W)).2 t htW htS x
    exact ⟨Sum.inl ⟨⟨a, ha⟩⟩, ht, y, hy⟩

def generalized : GeneralizedRicciFlowData.{u} where
  slice := slice W
  interval := W.interval
  interval_connected := W.interval_connected
  interval_nontrivial := W.interval_nontrivial
  slice_nonempty_iff := slice_nonempty_iff W
  metric := metric W
  connection := connection W
  space_topology := BoxTopology.topology (atlasBox W L)
  space_t2 := BoxTopology.t2Space (atlasBox W L)
    (atlasBox_vertical_compatibility W L) (atlasBox_covers W L)
  space_secondCountable := BoxTopology.secondCountable (atlasBox W L)
    (atlasBox_vertical_compatibility W L) (atlasBox_covers W L)
  time_continuous := BoxTopology.time_continuous (atlasBox W L)
  slice_embedding := BoxTopology.slice_embedding (atlasBox W L)
    (atlasBox_vertical_compatibility W L) (atlasBox_covers W L)
  box_index := BoxIndex W
  box := atlasBox W L
  box_openEmbedding := BoxTopology.spaceMap_openEmbedding (atlasBox W L)
    (atlasBox_vertical_compatibility W L)
  box_covers := atlasBox_covers W L
  vertical_compatibility := atlasBox_vertical_compatibility W L

end PoincareConjecture.Surgery.RegularHistory
