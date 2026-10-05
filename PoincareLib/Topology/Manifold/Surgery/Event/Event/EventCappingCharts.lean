import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingPatchSmooth
import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingCharts

/-!
# The actual capped discarded-side atlas

Ordinary charts of the discarded interior and the finite actual cap
patches form a smooth Hausdorff quotient. Every map is built from the
event's given collars and the inherited old manifold charts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]

/-- Old charts and new cap charts have disjoint index types. -/
abbrev EventCappingIndex := eventDiscardedOpen F T hT ⊕ Fin (F.event T hT).cap_count

/-- The Euclidean domain of each actual old or new patch. -/
abbrev eventCappingDomain : EventCappingIndex F T hT → TopologicalSpace.Opens StandardCapSpace
  | .inl x => ⟨(chartAt StandardCapSpace x).target, (chartAt StandardCapSpace x).open_target⟩
  | .inr _ => capDoubleBall

/-- Every indexed patch contains a point: the old chart center or the new
ball center. This does not assume the discarded interior is nonempty. -/
instance eventCappingDomain_nonempty (j : EventCappingIndex F T hT) :
    Nonempty (eventCappingDomain F T hT j) := by
  cases j with
  | inl x => exact ⟨⟨chartAt StandardCapSpace x x,
      (chartAt StandardCapSpace x).map_source (mem_chart_source _ x)⟩⟩
  | inr i => exact capDoubleBall_nonempty

/-- The same nonemptiness instance for the set-subtype presentation used
by the quotient chart API. -/
instance eventCappingDomain_set_nonempty (j : EventCappingIndex F T hT) :
    Nonempty ↥(eventCappingDomain F T hT j : Set StandardCapSpace) :=
  eventCappingDomain_nonempty F T hT j

variable (P : ∀ i, EventCapCoordinates F T hT i)

/-- Each patch maps partially into the same actual discarded interior. -/
noncomputable def eventCappingMap (j : EventCappingIndex F T hT) :
    OpenPartialHomeomorph (eventCappingDomain F T hT j) (eventDiscardedOpen F T hT) :=
  match j with
  | .inl x => (chartAt StandardCapSpace x).symm.subtypeRestr
      (eventCappingDomain_nonempty F T hT (.inl x))
  | .inr i => (P i).attachmentChart

/-- Old chart maps are defined on their whole Euclidean patch. -/
theorem eventCappingMap_old_source (x : eventDiscardedOpen F T hT) :
    (eventCappingMap F T hT P (.inl x)).source = Set.univ := by
  change ((chartAt StandardCapSpace x).symm.subtypeRestr
    (eventCappingDomain_nonempty F T hT (.inl x))).source = _
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  ext z
  exact iff_of_true z.property (Set.mem_univ _)

/-- The old chart maps are open embeddings with their literal chart images. -/
theorem eventCappingMap_old_openEmbedding (x : eventDiscardedOpen F T hT) :
    IsOpenEmbedding (eventCappingMap F T hT P (.inl x)) :=
  (eventCappingMap F T hT P (.inl x)).isOpenEmbedding
    (eventCappingMap_old_source F T hT P x)

/-- The actual patch maps and inverses are smooth in the quotient's
singleton Euclidean chart structures. -/
theorem eventCappingMap_smooth (j : EventCappingIndex F T hT) :
    letI := (eventCappingDomain F T hT j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (eventCappingMap F T hT P j)
        (eventCappingMap F T hT P j).source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (eventCappingMap F T hT P j).symm
        (eventCappingMap F T hT P j).target := by
  cases j with
  | inl x =>
      exact singletonPartialSubtype_smooth (chartAt StandardCapSpace x).symm
        (eventCappingDomain F T hT (.inl x)) (eventCappingDomain_nonempty F T hT (.inl x))
        contMDiffOn_chart_symm contMDiffOn_chart
  | inr i => exact (P i).attachmentChart_smooth

/-- The actual off-diagonal patch identifications have closed graphs. -/
theorem eventCappingMap_graph_closed (j k : EventCappingIndex F T hT) (hjk : j ≠ k) :
    IsClosed {q : eventCappingDomain F T hT j × eventCappingDomain F T hT k |
      q.1 ∈ (eventCappingMap F T hT P j).source ∧
      q.2 ∈ (eventCappingMap F T hT P k).source ∧
      eventCappingMap F T hT P j q.1 = eventCappingMap F T hT P k q.2} := by
  cases j with
  | inl x =>
      cases k with
      | inl y =>
          simp only [eventCappingMap_old_source, Set.mem_univ, true_and]
          exact isClosed_eq
            ((eventCappingMap_old_openEmbedding F T hT P x).continuous.comp continuous_fst)
            ((eventCappingMap_old_openEmbedding F T hT P y).continuous.comp continuous_snd)
      | inr i =>
          have h := (P i).attachmentChart_graph_closed.preimage
            (continuous_snd.prodMk
              ((eventCappingMap_old_openEmbedding F T hT P x).continuous.comp continuous_fst))
          simp only [eventCappingMap_old_source, Set.mem_univ, true_and]
          change IsClosed {q : eventCappingDomain F T hT (.inl x) × capDoubleBall |
            q.2 ∈ (P i).attachmentChart.source ∧
              eventCappingMap F T hT P (.inl x) q.1 = (P i).attachmentChart q.2}
          have hset : {q : eventCappingDomain F T hT (.inl x) × capDoubleBall |
              q.2 ∈ (P i).attachmentChart.source ∧
                eventCappingMap F T hT P (.inl x) q.1 = (P i).attachmentChart q.2} =
              {q : eventCappingDomain F T hT (.inl x) × capDoubleBall |
                q.2 ∈ (P i).attachmentChart.source ∧
                  (P i).attachmentChart q.2 = eventCappingMap F T hT P (.inl x) q.1} := by
            ext q
            exact and_congr Iff.rfl eq_comm
          rw [hset]
          exact h
  | inr i =>
      cases k with
      | inl y =>
          have h := (P i).attachmentChart_graph_closed.preimage
            (continuous_fst.prodMk
              ((eventCappingMap_old_openEmbedding F T hT P y).continuous.comp continuous_snd))
          simp only [eventCappingMap_old_source, Set.mem_univ, true_and]
          exact h
      | inr l =>
          have hil : i ≠ l := fun h => hjk (congrArg Sum.inr h)
          have hempty : {q : capDoubleBall × capDoubleBall |
              q.1 ∈ (P i).attachmentChart.source ∧ q.2 ∈ (P l).attachmentChart.source ∧
                (P i).attachmentChart q.1 = (P l).attachmentChart q.2} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro q ⟨hx, hy, heq⟩
            exact Set.disjoint_left.mp ((P i).attachmentChart_targets_disjoint (P l) hil)
              ((P i).attachmentChart.map_source hx)
              (heq.symm ▸ (P l).attachmentChart.map_source hy)
          change IsClosed {q : capDoubleBall × capDoubleBall |
            q.1 ∈ (P i).attachmentChart.source ∧ q.2 ∈ (P l).attachmentChart.source ∧
              (P i).attachmentChart q.1 = (P l).attachmentChart q.2}
          rw [hempty]
          exact isClosed_empty

/-- The quotient's overlap system is built from the actual patch maps. -/
noncomputable def eventCappingOverlap :=
  cappingOverlap (eventCappingMap F T hT P)

/-- The capped discarded space is the quotient of its ordinary and cap
patches by the actual annular identifications. -/
abbrev CappedDiscardedSpace := Quotient (eventCappingOverlap F T hT P).setoid

/-- The actual quotient is Hausdorff. -/
theorem cappedDiscardedSpace_t2 : T2Space (CappedDiscardedSpace F T hT P) :=
  cappingOverlap_t2 (fun j => (eventCappingDomain F T hT j : Set StandardCapSpace))
    (eventCappingMap F T hT P) (eventCappingMap_graph_closed F T hT P)

/-- The Euclidean quotient charts define the capped carrier's atlas. -/
@[implicit_reducible]
noncomputable def cappedDiscardedChartedSpace :
    ChartedSpace StandardCapSpace (CappedDiscardedSpace F T hT P) :=
  Poincare.Gluing.quotientChartedSpace
    (fun j => (eventCappingDomain F T hT j : Set StandardCapSpace))
    (fun j => (eventCappingDomain F T hT j).isOpen) (eventCappingOverlap F T hT P)

/-- The quotient's atlas is smooth because its actual transitions are. -/
theorem cappedDiscardedSpace_isManifold :
    letI := cappedDiscardedChartedSpace F T hT P
    IsManifold (𝓡 3) ∞ (CappedDiscardedSpace F T hT P) :=
  Poincare.Gluing.quotient_isManifold
    (fun j => (eventCappingDomain F T hT j : Set StandardCapSpace))
    (fun j => (eventCappingDomain F T hT j).isOpen) (eventCappingOverlap F T hT P)
    (cappingOverlap_smooth _ _ _ (eventCappingMap_smooth F T hT P))

end PoincareMT.M38
