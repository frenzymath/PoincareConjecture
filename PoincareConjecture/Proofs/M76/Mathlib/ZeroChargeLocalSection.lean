import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPresentation
import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalSegments










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem HasAlexanderCurvePresentation.exists_local_polygon_of_nonisolated
    {S : Set E} (h : HasAlexanderCurvePresentation S 0)
    {q : E} (hq : q ∈ S) (hacc : q ∈ closure (S \ {q})) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)),
      Function.Injective P ∧ P.HasSimplicialEdges ∧ q ∈ P.boundary ℝ ∧
      P.boundary ℝ ⊆ S ∧
      ∀ᶠ x in 𝓝 q, x ∈ S ↔ x ∈ P.boundary ℝ := by
  classical
  obtain ⟨m, n, P, r, hP, hr, hcover, _, hcount⟩ := h
  have hpair := (alexanderCurveCount_eq_zero_iff (fun i => (P i).boundary ℝ)).mp hcount
  have hclosed : IsClosed (⋃ i, (P i).boundary ℝ) :=
    isClosed_iUnion_of_finite (fun i => (P i).isClosed_boundary)
  have hqunion : q ∈ ⋃ i, (P i).boundary ℝ := by
    by_contra hnot
    have hqr : q ∈ r := ((hcover ▸ hq) : q ∈ r ∪ ⋃ i, (P i).boundary ℝ).resolve_right hnot
    have hrq := hr.eq_singleton_of_mem hqr
    have hsub : S \ {q} ⊆ ⋃ i, (P i).boundary ℝ := by
      intro x hx
      rcases hcover.subset hx.1 with hxr | hxP
      · exact (hx.2 (hrq ▸ hxr)).elim
      · exact hxP
    exact hnot (closure_minimal hsub hclosed hacc)
  obtain ⟨i, hqi⟩ := mem_iUnion.mp hqunion
  have hother (j : Fin m) : ∀ᶠ x in 𝓝 q,
      x ∈ (P j).boundary ℝ → x ∈ (P i).boundary ℝ := by
    by_cases hji : j = i
    · subst j
      exact Eventually.of_forall fun _ hx => hx
    · have hqj : q ∉ (P j).boundary ℝ :=
        fun hqj => disjoint_left.mp (hpair hji) hqj hqi
      filter_upwards [(P j).isClosed_boundary.isOpen_compl.mem_nhds hqj] with x hx
      exact fun hxj => (hx hxj).elim
  have hresidue : ∀ᶠ x in 𝓝 q, x ∈ r → x ∈ (P i).boundary ℝ := by
    by_cases hqr : q ∈ r
    · exact Eventually.of_forall fun x hx => (hr hx hqr).symm ▸ hqi
    · filter_upwards [hr.finite.isClosed.isOpen_compl.mem_nhds hqr] with x hx
      exact fun hxr => (hx hxr).elim
  have hsub : (P i).boundary ℝ ⊆ S :=
    fun x hx => hcover.symm.subset (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
  refine ⟨n i, P i, (hP i).1, (hP i).2, hqi, hsub, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hother, hresidue] with x hx hrx
  constructor
  · intro hxS
    rcases hcover.subset hxS with hxr | hxP
    · exact hrx hxr
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxP
      exact hx j hxj
  · exact fun hxP => hsub hxP





theorem HasAlexanderCurvePresentation.exists_local_segments_of_nonisolated
    {S : Set E} (h : HasAlexanderCurvePresentation S 0)
    {q : E} (hq : q ∈ S) (hacc : q ∈ closure (S \ {q})) :
    ∃ u v : E, u ≠ q ∧ v ≠ q ∧
      segment ℝ q u ∩ segment ℝ q v = {q} ∧
      segment ℝ q u ∪ segment ℝ q v ⊆ S ∧
      ∀ᶠ x in 𝓝 q, x ∈ S ↔ x ∈ segment ℝ q u ∪ segment ℝ q v := by
  obtain ⟨n, P, hinj, hP, hqP, hsub, hlocal⟩ :=
    h.exists_local_polygon_of_nonisolated hq hacc
  obtain ⟨u, v, hu, hv, hinter, hpair, hnear⟩ := P.exists_local_segment_pair hP hinj hqP
  refine ⟨u, v, hu, hv, hinter, hpair.trans hsub, ?_⟩
  filter_upwards [hlocal, hnear] with x hx hy
  exact hx.trans hy





theorem HasAlexanderCurvePresentation.local_germ_alternatives
    {S : Set E} (h : HasAlexanderCurvePresentation S 0) {q : E} (hq : q ∈ S) :
    (∀ᶠ x in 𝓝 q, x ∈ S ↔ x = q) ∨
      ∃ u v : E, u ≠ q ∧ v ≠ q ∧
        segment ℝ q u ∩ segment ℝ q v = {q} ∧
        segment ℝ q u ∪ segment ℝ q v ⊆ S ∧
        ∀ᶠ x in 𝓝 q, x ∈ S ↔ x ∈ segment ℝ q u ∪ segment ℝ q v := by
  by_cases hacc : q ∈ closure (S \ {q})
  · exact Or.inr (h.exists_local_segments_of_nonisolated hq hacc)
  · left
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hacc] with x hx
    constructor
    · intro hxS
      by_contra hxq
      exact hx (subset_closure ⟨hxS, hxq⟩)
    · rintro rfl
      exact hq

end Set
