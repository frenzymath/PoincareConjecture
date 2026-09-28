import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.OrdinaryModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}

theorem OrdinaryDoubleCurveModel.component_counts (M : OrdinaryDoubleCurveModel e f R) :
    doubleBoundaryComponentCount f D2 Q2 = {i | (M.pieces i ∩ Q2).Nonempty}.ncard ∧
    doubleInteriorComponentCount f D2 Q2 = {i | Disjoint (M.pieces i) Q2}.ncard := by
  have : Finite M.Index := M.finiteIndex
  exact connected_components_mark_counts_of_ambient_partition M.pieces
    (fun i ↦ (M.compact i).isClosed) M.disjoint M.cover M.connected Q2

theorem OrdinaryDoubleCurveModel.interval_iff_meets_rim
    (M : OrdinaryDoubleCurveModel e f R) (i : M.Index) :
    IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ Q2) ↔
      (M.pieces i ∩ Q2).Nonempty := by
  constructor
  · intro h
    obtain ⟨a, b, _, hab⟩ := h.exists_boundary_eq_pair
    rw [hab]
    exact ⟨a, Or.inl rfl⟩
  · intro h
    rcases M.models i with hi | ⟨_, _, _, _, _, hd⟩
    · exact hi
    · exact (Set.not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp hd) h).elim

theorem OrdinaryDoubleCurveModel.exists_interval_of_boundary_count_pos
    (M : OrdinaryDoubleCurveModel e f R)
    (h : 0 < doubleBoundaryComponentCount f D2 Q2) :
    ∃ i : M.Index, IsFinitePLBallPair ℝ (M.pieces i) (M.pieces i ∩ Q2) := by
  have : Finite M.Index := M.finiteIndex
  rw [M.component_counts.1] at h
  obtain ⟨i, hi⟩ := (Set.ncard_pos (Set.toFinite _)).mp h
  exact ⟨i, (M.interval_iff_meets_rim i).mpr hi⟩

theorem OrdinaryDoubleCurveModel.exists_polygon_of_interior_count_pos
    (M : OrdinaryDoubleCurveModel e f R)
    (h : 0 < doubleInteriorComponentCount f D2 Q2) :
    ∃ (i : M.Index) (n : ℕ) (P : Polygon V2 (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = M.pieces i ∧ Disjoint (M.pieces i) Q2 := by
  have : Finite M.Index := M.finiteIndex
  rw [M.component_counts.2] at h
  obtain ⟨i, hi⟩ := (Set.ncard_pos (Set.toFinite _)).mp h
  rcases M.models i with hball | hpoly
  · have hmeet := (M.interval_iff_meets_rim i).mp hball
    exact (Set.not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp hi) hmeet).elim
  · exact ⟨i, hpoly⟩

theorem OrdinaryDoubleCurveModel.counts_zero_iff_double_locus_empty
    (M : OrdinaryDoubleCurveModel e f R) :
    (doubleBoundaryComponentCount f D2 Q2 = 0 ∧
      doubleInteriorComponentCount f D2 Q2 = 0) ↔ doubleLocusOn f D2 = ∅ := by
  have : Finite M.Index := M.finiteIndex
  rw [M.component_counts.1, M.component_counts.2]
  constructor
  · rintro ⟨hb, hi⟩
    have hb' := (Set.ncard_eq_zero (Set.toFinite _)).mp hb
    have hi' := (Set.ncard_eq_zero (Set.toFinite _)).mp hi
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, hix⟩ := mem_iUnion.mp (M.cover.symm ▸ hx)
    by_cases hmeet : (M.pieces i ∩ Q2).Nonempty
    · exact Set.notMem_empty i (hb' ▸ hmeet)
    · have hd : Disjoint (M.pieces i) Q2 :=
        disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet)
      exact Set.notMem_empty i (hi' ▸ hd)
  · intro h
    have hn : ∀ i : M.Index, False := by
      intro i
      obtain ⟨x, hx⟩ := (M.connected i).nonempty
      have hxG : x ∈ doubleLocusOn f D2 := M.cover ▸ mem_iUnion.mpr ⟨i, hx⟩
      exact Set.notMem_empty x (h ▸ hxG)
    constructor <;> apply (Set.ncard_eq_zero (Set.toFinite _)).mpr <;>
      exact Set.eq_empty_iff_forall_notMem.mpr (fun i _ ↦ hn i)

theorem doubleLocusOn_eq_empty_iff_injOn {E Y : Type*} (g : E → Y) (S : Set E) :
    doubleLocusOn g S = ∅ ↔ InjOn g S := by
  constructor
  · intro h x hx y hy hxy
    by_contra hne
    exact Set.notMem_empty x (h ▸ (show x ∈ doubleLocusOn g S from ⟨hx, y, hy, hxy, hne⟩))
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, y, hy, hxy, hne⟩
    exact hne (h hx hy hxy)

theorem OrdinaryDoubleCurveModel.isEmbedding_of_counts_zero [T2Space X]
    (M : OrdinaryDoubleCurveModel e f R) (hf : ContinuousOn f D2)
    (hb : doubleBoundaryComponentCount f D2 Q2 = 0)
    (hi : doubleInteriorComponentCount f D2 Q2 = 0) :
    IsEmbedding (fun x : D2 ↦ f x) := by
  have hinj := (doubleLocusOn_eq_empty_iff_injOn f D2).mp
    (M.counts_zero_iff_double_locus_empty.mp ⟨hb, hi⟩)
  exact (hf.domRestrict.isClosedEmbedding
    (fun x y h ↦ Subtype.ext (hinj x.property y.property h))).isEmbedding

theorem OrdinaryDoubleCurveModel.isEmbedding_of_PL_counts_zero [T2Space X]
    (M : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (hb : doubleBoundaryComponentCount f D2 Q2 = 0)
    (hi : doubleInteriorComponentCount f D2 Q2 = 0) :
    IsEmbedding (fun x : D2 ↦ f x) :=
  M.isEmbedding_of_counts_zero hf.continuousOn hb hi

end PoincareConjecture.M76.Dehn
