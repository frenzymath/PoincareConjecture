import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# A connected image cannot cross a bounded frontier

A real-valued barrier excludes the actual ambient frontier of an open set.
Connectedness and one included point then put the whole image inside.
Source: Morgan--Tian pp. 263-265; M28 derivation 143.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

/-- A connected set meeting an open set stays inside it when a real
barrier separates it from the global frontier. No continuity of the
barrier itself is needed. Source: M28 derivation 143. -/
theorem IsConnected.subset_of_frontier_barrier
    {X : Type*} [TopologicalSpace X] {S U : Set X}
    (hS : IsConnected S) (hU : IsOpen U) (f : X → ℝ) {B : ℝ}
    (hfront : ∀ x ∈ frontier U, f x ≤ B)
    (hhigh : ∀ x ∈ S, B < f x)
    (hmeet : (S ∩ U).Nonempty) : S ⊆ U := by
  let _ : ConnectedSpace S := Subtype.connectedSpace hS
  have hdisjoint : Disjoint (frontier U) S := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge (hfront x hx)) (hhigh x hy)
  have hclopen : IsClopen ((Subtype.val : S → X) ⁻¹' U) :=
    isClopen_preimage_val hU hdisjoint
  obtain ⟨p, hpS, hpU⟩ := hmeet
  have hfull := hclopen.eq_univ ⟨⟨p, hpS⟩, hpU⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : S) ∈ (univ : Set S) := mem_univ _
  rw [← hfull] at hmem
  exact hmem

/-- Uniformly diverging barrier values on connected moving images
eventually put those images inside the same open region. Its frontier
is compact in the full ambient space. Source: M28 derivation 143. -/
theorem eventually_image_subset_of_compact_frontier_barrier
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {I : Type*} {l : Filter I} {U : Set X} (hU : IsOpen U)
    (hcompact : IsCompact (frontier U)) (f : X → ℝ)
    (hf : ContinuousOn f (frontier U))
    {S : Set Y} (hS : IsConnected S)
    (e : I → Y → X) (he : ∀ i, ContinuousOn (e i) S)
    {p : Y} (hp : p ∈ S) (hcenter : ∀ i, e i p ∈ U)
    (L : I → ℝ) (hL : Tendsto L l atTop)
    (hlower : ∀ᶠ i in l, ∀ x ∈ S, L i ≤ f (e i x)) :
    ∀ᶠ i in l, e i '' S ⊆ U := by
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hf
  filter_upwards [hL.eventually_gt_atTop B, hlower] with i hi hbound
  apply (hS.image (e i) (he i)).subset_of_frontier_barrier hU f
  · intro x hx
    exact hB (mem_image_of_mem f hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact hi.trans_le (hbound x hx)
  · exact ⟨e i p, ⟨p, hp, rfl⟩, hcenter i⟩
