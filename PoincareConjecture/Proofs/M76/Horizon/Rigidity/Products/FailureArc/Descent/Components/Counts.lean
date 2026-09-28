import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.Decomposition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Topology.Mathlib.FiniteClosedComponentPartition

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
  {S Q : Set E} {R : Set X}

open Classical in
abbrev SourceDoubleComponents.Index (M : SourceDoubleComponents e f S Q R) :=
  M.graph.vertexAbstractComplex.edgeGraph.ConnectedComponent

theorem SourceDoubleComponents.literal_cover (M : SourceDoubleComponents e f S Q R) :
    ⋃ i, M.pieces i = doubleLocusOn f S := M.cover.symm.trans M.space

theorem SourceDoubleComponents.compact (M : SourceDoubleComponents e f S Q R) (i : M.Index) :
    IsCompact (M.pieces i) := (M.topology i).1

theorem SourceDoubleComponents.connected (M : SourceDoubleComponents e f S Q R) (i : M.Index) :
    IsConnected (M.pieces i) := (M.topology i).2.1

theorem SourceDoubleComponents.pieces_subset (M : SourceDoubleComponents e f S Q R)
    (i : M.Index) : M.pieces i ⊆ M.graph.space :=
  fun _ hx => M.cover.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)

theorem SourceDoubleComponents.component_counts (M : SourceDoubleComponents e f S Q R) :
    doubleBoundaryComponentCount f S Q = {i | (M.pieces i ∩ Q).Nonempty}.ncard ∧
    doubleInteriorComponentCount f S Q = {i | Disjoint (M.pieces i) Q}.ncard := by
  have : Finite M.Index := M.finite_components
  exact connected_components_mark_counts_of_ambient_partition M.pieces
    (fun i ↦ (M.compact i).isClosed) M.disjoint M.literal_cover M.connected Q

theorem SourceDoubleComponents.interval_iff_meets_rim
    (M : SourceDoubleComponents e f S Q R) (i : M.Index) :
    IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ Q) ↔
      (M.pieces i ∩ Q).Nonempty := by
  constructor
  · intro h
    obtain ⟨a, b, _, hab⟩ := h.exists_boundary_eq_pair
    rw [hab]
    exact ⟨a, Or.inl rfl⟩
  · intro h
    rcases M.models i with hi | ⟨_, _, _, _, _, hd⟩
    · exact hi
    · exact (Set.not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp hd) h).elim

theorem SourceDoubleComponents.exists_interval_of_boundary_count_pos
    (M : SourceDoubleComponents e f S Q R)
    (h : 0 < doubleBoundaryComponentCount f S Q) :
    ∃ i : M.Index, IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ Q) := by
  have : Finite M.Index := M.finite_components
  rw [M.component_counts.1] at h
  obtain ⟨i, hi⟩ := (Set.ncard_pos (Set.toFinite _)).mp h
  exact ⟨i, (M.interval_iff_meets_rim i).mpr hi⟩

theorem SourceDoubleComponents.exists_polygon_of_interior_count_pos
    (M : SourceDoubleComponents e f S Q R)
    (h : 0 < doubleInteriorComponentCount f S Q) :
    ∃ (i : M.Index) (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = M.pieces i ∧ Disjoint (M.pieces i) Q := by
  have : Finite M.Index := M.finite_components
  rw [M.component_counts.2] at h
  obtain ⟨i, hi⟩ := (Set.ncard_pos (Set.toFinite _)).mp h
  rcases M.models i with hball | hpoly
  · have hmeet := (M.interval_iff_meets_rim i).mp hball
    exact (Set.not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp hi) hmeet).elim
  · exact ⟨i, hpoly⟩

theorem SourceDoubleComponents.counts_zero_iff_double_locus_empty
    (M : SourceDoubleComponents e f S Q R) :
    (doubleBoundaryComponentCount f S Q = 0 ∧
      doubleInteriorComponentCount f S Q = 0) ↔ doubleLocusOn f S = ∅ := by
  have : Finite M.Index := M.finite_components
  rw [M.component_counts.1, M.component_counts.2]
  constructor
  · rintro ⟨hb, hi⟩
    have hb' := (Set.ncard_eq_zero (Set.toFinite _)).mp hb
    have hi' := (Set.ncard_eq_zero (Set.toFinite _)).mp hi
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, hix⟩ := mem_iUnion.mp (M.literal_cover.symm ▸ hx)
    by_cases hmeet : (M.pieces i ∩ Q).Nonempty
    · exact Set.notMem_empty i (hb' ▸ hmeet)
    · have hd : Disjoint (M.pieces i) Q :=
        disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet)
      exact Set.notMem_empty i (hi' ▸ hd)
  · intro h
    have hn : ∀ i : M.Index, False := by
      intro i
      obtain ⟨x, hx⟩ := (M.connected i).nonempty
      have hxG : x ∈ doubleLocusOn f S := M.literal_cover ▸ mem_iUnion.mpr ⟨i, hx⟩
      exact Set.notMem_empty x (h ▸ hxG)
    constructor <;> apply (Set.ncard_eq_zero (Set.toFinite _)).mpr <;>
      exact Set.eq_empty_iff_forall_notMem.mpr (fun i _ ↦ hn i)

theorem SourceDoubleComponents.isEmbedding_of_counts_zero [T2Space X]
    (M : SourceDoubleComponents e f S Q R) (hS : IsCompact S)
    (hf : ContinuousOn f S)
    (hb : doubleBoundaryComponentCount f S Q = 0)
    (hi : doubleInteriorComponentCount f S Q = 0) :
    IsEmbedding (fun x : S => f x) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hnone := M.counts_zero_iff_double_locus_empty.mp ⟨hb, hi⟩
  apply (hf.domRestrict.isClosedEmbedding ?_).isEmbedding
  intro x y h
  apply Subtype.ext
  by_contra hne
  exact Set.notMem_empty (x : E) (hnone ▸
    (show (x : E) ∈ doubleLocusOn f S from ⟨x.property, y, y.property, h, hne⟩))

end PoincareConjecture.M76.Dehn.Annuli
