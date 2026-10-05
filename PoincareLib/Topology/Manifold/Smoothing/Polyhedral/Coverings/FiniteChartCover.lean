import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Separation.Regular

/-!
# Finite chart covers with compact containment

This is the compact-space preparation for Hamilton 1976, Theorem 2(1),
printed p. 69. The proof uses only compact Hausdorff topology and applies
to arbitrary model spaces. See M76 derivation 03. No compatibility stronger
than continuity is claimed for the transition maps.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace ChartedSpace

variable (H : Type*) {M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [CompactSpace M]

/-- A compact charted space has a finite cover by preferred chart sources.
This is the compact case of Hamilton's chart cover on p. 69; see derivation 03. -/
theorem exists_finite_chart_cover :
    ∃ t : Finset M, ⋃ x ∈ t, (chartAt H x).source = univ :=
  finite_cover_nhds (chart_source_mem_nhds H)

variable [T2Space M]

/-- A compact charted space has a finite open cover whose closures stay inside
the corresponding chart sources. See Hamilton p. 69 and M76 derivation 03. -/
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

/-- Two nested shrinkings of a finite chart cover give compact containment
at both boundaries. These are the neighborhoods used before changing charts
on overlaps in Hamilton p. 69; see M76 derivation 03. -/
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
/-- Compact containment in a chart source gives a compact coordinate image.
Only continuity on the source is used; see M76 derivation 03. -/
theorem isCompact_chart_image_closure (x : M) {V : Set M}
    (hV : closure V ⊆ (chartAt H x).source) :
    IsCompact (chartAt H x '' closure V) :=
  isClosed_closure.isCompact.image_of_continuousOn ((chartAt H x).continuousOn.mono hV)

end ChartedSpace
