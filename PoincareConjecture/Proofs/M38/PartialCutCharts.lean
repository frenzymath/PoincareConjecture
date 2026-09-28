import PoincareConjecture.Proofs.M38.PartialCutPatches
import PoincareConjecture.Proofs.M38.CappingCharts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))

abbrev PartialCappingIndex := eventCutOpen F T hT P S ⊕ (S × Bool)

abbrev partialCappingDomain :
    PartialCappingIndex F T hT P S → TopologicalSpace.Opens StandardCapSpace
  | .inl x => ⟨(chartAt StandardCapSpace x).target, (chartAt StandardCapSpace x).open_target⟩
  | .inr _ => capDoubleBall

instance partialCappingDomain_nonempty (j : PartialCappingIndex F T hT P S) :
    Nonempty (partialCappingDomain F T hT P S j) := by
  cases j with
  | inl x => exact ⟨⟨chartAt StandardCapSpace x x,
      (chartAt StandardCapSpace x).map_source (mem_chart_source _ x)⟩⟩
  | inr a => exact capDoubleBall_nonempty

instance partialCappingDomain_set_nonempty (j : PartialCappingIndex F T hT P S) :
    Nonempty ↥(partialCappingDomain F T hT P S j : Set StandardCapSpace) :=
  partialCappingDomain_nonempty F T hT P S j

noncomputable def partialCappingMap (j : PartialCappingIndex F T hT P S) :
    OpenPartialHomeomorph (partialCappingDomain F T hT P S j) (eventCutOpen F T hT P S) :=
  match j with
  | .inl x => (chartAt StandardCapSpace x).symm.subtypeRestr
      (partialCappingDomain_nonempty F T hT P S (.inl x))
  | .inr a => cutAttachmentChart F T hT P S a

theorem partialCappingMap_old_source (x : eventCutOpen F T hT P S) :
    (partialCappingMap F T hT P S (.inl x)).source = Set.univ := by
  change ((chartAt StandardCapSpace x).symm.subtypeRestr
    (partialCappingDomain_nonempty F T hT P S (.inl x))).source = _
  rw [OpenPartialHomeomorph.subtypeRestr_source]
  ext z
  exact iff_of_true z.property (Set.mem_univ _)

theorem partialCappingMap_old_openEmbedding (x : eventCutOpen F T hT P S) :
    IsOpenEmbedding (partialCappingMap F T hT P S (.inl x)) :=
  (partialCappingMap F T hT P S (.inl x)).isOpenEmbedding
    (partialCappingMap_old_source F T hT P S x)

theorem partialCappingMap_smooth (j : PartialCappingIndex F T hT P S) :
    letI := (partialCappingDomain F T hT P S j).isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (partialCappingMap F T hT P S j)
        (partialCappingMap F T hT P S j).source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (partialCappingMap F T hT P S j).symm
        (partialCappingMap F T hT P S j).target := by
  cases j with
  | inl x =>
      exact singletonPartialSubtype_smooth (chartAt StandardCapSpace x).symm
        (partialCappingDomain F T hT P S (.inl x))
        (partialCappingDomain_nonempty F T hT P S (.inl x))
        contMDiffOn_chart_symm contMDiffOn_chart
  | inr a => exact cutAttachmentChart_smooth F T hT P S a

theorem partialCappingMap_graph_closed (j k : PartialCappingIndex F T hT P S) (hjk : j ≠ k) :
    IsClosed {q : partialCappingDomain F T hT P S j × partialCappingDomain F T hT P S k |
      q.1 ∈ (partialCappingMap F T hT P S j).source ∧
      q.2 ∈ (partialCappingMap F T hT P S k).source ∧
      partialCappingMap F T hT P S j q.1 = partialCappingMap F T hT P S k q.2} := by
  cases j with
  | inl x =>
      cases k with
      | inl y =>
          simp only [partialCappingMap_old_source, Set.mem_univ, true_and]
          exact isClosed_eq
            ((partialCappingMap_old_openEmbedding F T hT P S x).continuous.comp continuous_fst)
            ((partialCappingMap_old_openEmbedding F T hT P S y).continuous.comp continuous_snd)
      | inr a =>
          have h := (cutAttachmentChart_graph_closed F T hT P S a).preimage
            (continuous_snd.prodMk
              ((partialCappingMap_old_openEmbedding F T hT P S x).continuous.comp continuous_fst))
          simp only [partialCappingMap_old_source, Set.mem_univ, true_and]
          change IsClosed {q : partialCappingDomain F T hT P S (.inl x) × capDoubleBall |
            q.2 ∈ (cutAttachmentChart F T hT P S a).source ∧
              partialCappingMap F T hT P S (.inl x) q.1 = cutAttachmentChart F T hT P S a q.2}
          convert h using 1
          ext q
          exact and_congr Iff.rfl eq_comm
  | inr a =>
      cases k with
      | inl y =>
          have h := (cutAttachmentChart_graph_closed F T hT P S a).preimage
            (continuous_fst.prodMk
              ((partialCappingMap_old_openEmbedding F T hT P S y).continuous.comp continuous_snd))
          simp only [partialCappingMap_old_source, Set.mem_univ, true_and]
          exact h
      | inr b =>
          have hab : a ≠ b := fun h => hjk (congrArg Sum.inr h)
          have hempty : {q : capDoubleBall × capDoubleBall |
              q.1 ∈ (cutAttachmentChart F T hT P S a).source ∧
              q.2 ∈ (cutAttachmentChart F T hT P S b).source ∧
              cutAttachmentChart F T hT P S a q.1 = cutAttachmentChart F T hT P S b q.2} = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro q ⟨hx, hy, heq⟩
            exact Set.disjoint_left.mp (cutAttachmentChart_targets_disjoint F T hT P S a b hab)
              ((cutAttachmentChart F T hT P S a).map_source hx)
              (heq.symm ▸ (cutAttachmentChart F T hT P S b).map_source hy)
          change IsClosed {q : capDoubleBall × capDoubleBall |
            q.1 ∈ (cutAttachmentChart F T hT P S a).source ∧
            q.2 ∈ (cutAttachmentChart F T hT P S b).source ∧
            cutAttachmentChart F T hT P S a q.1 = cutAttachmentChart F T hT P S b q.2}
          rw [hempty]
          exact isClosed_empty

noncomputable def partialCappingOverlap := cappingOverlap (partialCappingMap F T hT P S)

abbrev PartialCappedSpace := Quotient (partialCappingOverlap F T hT P S).setoid

theorem partialCappedSpace_t2 : T2Space (PartialCappedSpace F T hT P S) :=
  cappingOverlap_t2 (fun j => (partialCappingDomain F T hT P S j : Set StandardCapSpace))
    (partialCappingMap F T hT P S) (partialCappingMap_graph_closed F T hT P S)

@[implicit_reducible]
noncomputable def partialCappedChartedSpace :
    ChartedSpace StandardCapSpace (PartialCappedSpace F T hT P S) :=
  Poincare.Gluing.quotientChartedSpace
    (fun j => (partialCappingDomain F T hT P S j : Set StandardCapSpace))
    (fun j => (partialCappingDomain F T hT P S j).isOpen) (partialCappingOverlap F T hT P S)

theorem partialCappedSpace_isManifold :
    letI := partialCappedChartedSpace F T hT P S
    IsManifold (𝓡 3) ∞ (PartialCappedSpace F T hT P S) :=
  Poincare.Gluing.quotient_isManifold
    (fun j => (partialCappingDomain F T hT P S j : Set StandardCapSpace))
    (fun j => (partialCappingDomain F T hT P S j).isOpen) (partialCappingOverlap F T hT P S)
    (cappingOverlap_smooth _ _ _ (partialCappingMap_smooth F T hT P S))

end PoincareConjecture.M38
