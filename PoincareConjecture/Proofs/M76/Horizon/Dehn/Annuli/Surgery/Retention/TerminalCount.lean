import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ComponentCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OrdinaryCounts

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.SourceCircleDecomposition

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → X} {S : Set E}



theorem component_count (M : SourceCircleDecomposition f S) :
    Nat.card (ConnectedComponents (doubleLocusOn f S)) = Nat.card M.Index := by
  have h := (connected_components_mark_counts_of_ambient_partition M.pieces
    (fun i ↦ (M.pieces_isCompact i).isClosed) M.disjoint
    (M.cover.symm.trans M.space) M.pieces_isConnected (∅ : Set E)).2
  simpa only [preimage_empty, image_empty, compl_empty, Set.disjoint_empty,
    ofPred_true, Set.ncard_univ] using h


theorem exists_component_of_count_pos (M : SourceCircleDecomposition f S)
    (h : 0 < Nat.card (ConnectedComponents (doubleLocusOn f S))) :
    Nonempty M.Index := by
  rw [M.component_count] at h
  exact Nat.card_pos_iff.mp h |>.1


theorem component_count_zero_iff_injOn (M : SourceCircleDecomposition f S) :
    Nat.card (ConnectedComponents (doubleLocusOn f S)) = 0 ↔ InjOn f S := by
  rw [M.component_count, ← doubleLocusOn_eq_empty_iff_injOn]
  constructor
  · intro h
    have hempty : IsEmpty M.Index := (Nat.card_eq_zero.mp h).resolve_right
      (fun hinf ↦ hinf.false)
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, _⟩ := mem_iUnion.mp (M.cover.subset (M.space.symm.subset hx))
    exact hempty.false i
  · intro h
    have hempty : IsEmpty M.Index := ⟨fun i ↦ by
      obtain ⟨x, hx⟩ := (M.pieces_isConnected i).nonempty
      exact Set.notMem_empty x (h ▸ M.piece_subset_double i hx)⟩
    exact Nat.card_eq_zero.mpr (Or.inl hempty)


theorem isEmbedding_of_component_count_zero [TopologicalSpace X] [T2Space X]
    (M : SourceCircleDecomposition f S) (hS : IsCompact S) (hf : ContinuousOn f S)
    (hzero : Nat.card (ConnectedComponents (doubleLocusOn f S)) = 0) :
    IsEmbedding (fun x : S ↦ f x) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hi := M.component_count_zero_iff_injOn.mp hzero
  exact (hf.domRestrict.isClosedEmbedding
    (fun x y h ↦ Subtype.ext (hi x.property y.property h))).isEmbedding

end PoincareConjecture.M76.Dehn.Annuli.SourceCircleDecomposition
