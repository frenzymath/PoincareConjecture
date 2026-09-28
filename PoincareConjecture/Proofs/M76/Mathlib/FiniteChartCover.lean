import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

open Set
open scoped Topology

namespace ChartedSpace

variable (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [CompactSpace M]

theorem exists_finite_chart_cover :
    ∃ t : Finset M, ⋃ x ∈ t, (chartAt H x).source = univ :=
  finite_cover_nhds (chart_source_mem_nhds H)

variable [T2Space M]

theorem exists_finite_shrunk_chart_cover :
    ∃ t : Finset M, ∃ V : M → Set M,
      (∀ x, x ∈ V x) ∧ (∀ x, IsOpen (V x)) ∧
      (∀ x, closure (V x) ⊆ (chartAt H x).source) ∧
      (∀ x, IsCompact (closure (V x))) ∧ ⋃ x ∈ t, V x = univ := by
  have h : ∀ x : M, ∃ V : Set M,
      (x ∈ V ∧ IsOpen V) ∧ closure V ⊆ (chartAt H x).source :=
    fun x => (hasBasis_opens_closure x).mem_iff.mp (chart_source_mem_nhds H x)
  choose V hV hVs using h
  obtain ⟨t, ht⟩ := finite_cover_nhds (fun x => (hV x).2.mem_nhds (hV x).1)
  exact ⟨t, V, fun x => (hV x).1, fun x => (hV x).2, hVs,
    fun _ => isClosed_closure.isCompact, ht⟩

theorem exists_finite_nested_chart_cover :
    ∃ t : Finset M, ∃ V W : M → Set M,
      (∀ x, x ∈ W x) ∧ (∀ x, IsOpen (V x)) ∧ (∀ x, IsOpen (W x)) ∧
      (∀ x, closure (W x) ⊆ V x) ∧
      (∀ x, closure (V x) ⊆ (chartAt H x).source) ∧
      (∀ x, IsCompact (closure (V x))) ∧ ⋃ x ∈ t, W x = univ := by
  obtain ⟨_, V, hxV, hVo, hVs, hVc, _⟩ := exists_finite_shrunk_chart_cover H (M := M)
  have h : ∀ x : M, ∃ W : Set M, (x ∈ W ∧ IsOpen W) ∧ closure W ⊆ V x :=
    fun x => (hasBasis_opens_closure x).mem_iff.mp ((hVo x).mem_nhds (hxV x))
  choose W hW hWV using h
  obtain ⟨t, ht⟩ := finite_cover_nhds (fun x => (hW x).2.mem_nhds (hW x).1)
  exact ⟨t, V, W, fun x => (hW x).1, hVo, fun x => (hW x).2, hWV, hVs, hVc, ht⟩

omit [T2Space M] in

theorem isCompact_chart_image_closure (x : M) {V : Set M}
    (hV : closure V ⊆ (chartAt H x).source) :
    IsCompact (chartAt H x '' closure V) :=
  isClosed_closure.isCompact.image_of_continuousOn ((chartAt H x).continuousOn.mono hV)

end ChartedSpace
