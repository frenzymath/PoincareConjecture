import PoincareConjecture.Proofs.M07.Topology.Gluing.Basic
import Mathlib.Geometry.Manifold.ChartedSpace

open Set Topology

namespace Poincare.Gluing

universe u v

noncomputable section

variable {I : Type u} {E : Type v} [TopologicalSpace E]

variable (U : I → Set E) (hU : ∀ i, IsOpen (U i))

abbrev Piece (i : I) := U i

instance pieceTopologicalSpace (i : I) : TopologicalSpace (Piece U i) :=
  inferInstance

def quotientChart (D : OverlapSystem (fun i => Piece U i)) (i : I)
    [Nonempty (Piece U i)] [Nonempty E] :
    OpenPartialHomeomorph (Quotient D.setoid) E :=
  ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph).lift_openEmbedding
    (D.include_isOpenEmbedding i)

theorem quotientChart_apply (D : OverlapSystem (fun i => Piece U i)) (i : I)
    [Nonempty (Piece U i)] [Nonempty E] (x : Piece U i) :
    quotientChart U hU D i (D.include i x) = (x : E) := by
  simpa [quotientChart] using
    (OpenPartialHomeomorph.lift_openEmbedding_apply
      ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph)
      (D.include_isOpenEmbedding i) (x := x))

theorem quotientChart_source (D : OverlapSystem (fun i => Piece U i)) (i : I)
    [Nonempty (Piece U i)] [Nonempty E] :
    (quotientChart U hU D i).source =
      D.include i '' Set.univ := by
  simp [quotientChart]

theorem quotientChart_target (D : OverlapSystem (fun i => Piece U i)) (i : I)
    [Nonempty (Piece U i)] [Nonempty E] :
    (quotientChart U hU D i).target = U i := by
  simp [quotientChart]

theorem quotientChart_symm_apply (D : OverlapSystem (fun i => Piece U i)) (i : I)
    [Nonempty (Piece U i)] [Nonempty E] {x : E} (hx : x ∈ U i) :
    (quotientChart U hU D i).symm x = D.include i ⟨x, hx⟩ := by
  rw [quotientChart, OpenPartialHomeomorph.lift_openEmbedding_symm]
  change D.include i ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x) = _
  congr 1
  apply Subtype.ext
  exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
    (f := (Subtype.val : Piece U i → E))
    (h := (hU i).isOpenEmbedding_subtypeVal) (x := x)
    ⟨⟨x, hx⟩, rfl⟩)

theorem quotientChart_comp_mem_transition_source
    (D : OverlapSystem (fun i => Piece U i)) (i j : I)
    [Nonempty (Piece U i)] [Nonempty (Piece U j)] [Nonempty E] {x : E}
    (hx : x ∈
      ((quotientChart U hU D i).symm.trans (quotientChart U hU D j)).source) :
    ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x) ∈
      (D.transition i j).source := by
  rw [OpenPartialHomeomorph.trans_source] at hx
  have hxi : x ∈ U i := by
    rw [← quotientChart_target U hU D i]
    exact hx.1
  have hqj : (quotientChart U hU D i).symm x ∈
      (quotientChart U hU D j).source := hx.2
  rw [quotientChart_source U hU D j] at hqj
  rcases hqj with ⟨yj, _, hyj⟩
  have hsub :
      (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x =
        (⟨x, hxi⟩ : Piece U i) := by
    apply Subtype.ext
    exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (f := (Subtype.val : Piece U i → E))
      (h := (hU i).isOpenEmbedding_subtypeVal) (x := x)
      ⟨⟨x, hxi⟩, rfl⟩)
  have heq : D.include i
      ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x) =
      D.include j yj := by
    rw [hsub, ← quotientChart_symm_apply U hU D i hxi]
    exact hyj.symm
  exact (D.include_eq_iff i j _ _).mp heq |>.1

theorem quotientChart_comp_apply
    (D : OverlapSystem (fun i => Piece U i)) (i j : I)
    [Nonempty (Piece U i)] [Nonempty (Piece U j)] [Nonempty E] {x : E}
    (hx : x ∈
      ((quotientChart U hU D i).symm.trans (quotientChart U hU D j)).source) :
    ((quotientChart U hU D i).symm.trans (quotientChart U hU D j)) x =
      ((D.transition i j
        ((hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x) :
          Piece U j) : E) := by
  have hxi : x ∈ U i := by
    rw [← quotientChart_target U hU D i]
    exact (by
      rw [OpenPartialHomeomorph.trans_source] at hx
      exact hx.1)
  have hsrc := quotientChart_comp_mem_transition_source U hU D i j hx
  have hsub :
      (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm x =
        (⟨x, hxi⟩ : Piece U i) := by
    apply Subtype.ext
    exact (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (f := (Subtype.val : Piece U i → E))
      (h := (hU i).isOpenEmbedding_subtypeVal) (x := x)
      ⟨⟨x, hxi⟩, rfl⟩)
  rw [OpenPartialHomeomorph.trans_apply]
  rw [quotientChart_symm_apply U hU D i hxi]
  rw [← hsub]
  have hq := (D.include_eq_iff i j _ _).mpr ⟨hsrc, rfl⟩
  rw [hq]
  exact quotientChart_apply U hU D j (D.transition i j _)

theorem quotientChart_source_cover (D : OverlapSystem (fun i => Piece U i))
    [∀ i, Nonempty (Piece U i)] [Nonempty E] :
    (⋃ i, (quotientChart U hU D i).source) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | h a =>
      rcases a with ⟨i, x⟩
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [quotientChart_source U hU D i]
      change D.include i x ∈ D.include i '' (Set.univ : Set (Piece U i))
      exact ⟨x, Set.mem_univ _, rfl⟩

@[implicit_reducible]
def quotientChartedSpace (D : OverlapSystem (fun i => Piece U i))
    [∀ i, Nonempty (Piece U i)] [Nonempty E] :
    ChartedSpace E (Quotient D.setoid) := by
  let charts : I → OpenPartialHomeomorph (Quotient D.setoid) E :=
    fun i => quotientChart U hU D i
  have hcover : ∀ q : Quotient D.setoid, ∃ i : I, q ∈ (charts i).source := by
    intro q
    have hq : q ∈ ⋃ i, (charts i).source := by
      rw [quotientChart_source_cover U hU D]
      exact Set.mem_univ q
    rcases Set.mem_iUnion.mp hq with ⟨i, hi⟩
    exact ⟨i, hi⟩
  let indexAt : Quotient D.setoid → I := fun q => Classical.choose (hcover q)
  refine {
    atlas := Set.range charts
    chartAt := fun q => charts (indexAt q)
    mem_chart_source := fun q => Classical.choose_spec (hcover q)
    chart_mem_atlas := fun q => ⟨indexAt q, rfl⟩ }

theorem quotientChart_overlap_apply (D : OverlapSystem (fun i => Piece U i))
    (i j : I) [Nonempty (Piece U i)] [Nonempty (Piece U j)] [Nonempty E]
    (x : Piece U i) (hx : x ∈ (D.transition i j).source) :
    quotientChart U hU D j (D.include i x) =
      ((D.transition i j x : Piece U j) : E) := by
  have hq : D.include i x = D.include j (D.transition i j x) :=
    (D.include_eq_iff i j x (D.transition i j x)).mpr ⟨hx, rfl⟩
  rw [hq]
  exact quotientChart_apply U hU D j (D.transition i j x)

end

end Poincare.Gluing
