import PoincareConjecture.Proofs.M76.Mathlib.RegularEdgeCrossing
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Perfect

set_option autoImplicit false
open Set Geometry
universe u

namespace PoincareConjecture.M76.PeriodicSquare

theorem vertex_has_edge_of_no_isolated_points
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2)
    (hno : ∀ x : L.space, ¬IsOpen ({x} : Set L.space)) :
    ∀ v ∈ L.vertices, ∃ s ∈ L.faces, s.card = 2 ∧ v ∈ s := by
  classical
  intro v hv
  by_contra hn
  have hsmall (s : Finset E) (hs : s ∈ L.faces) (hvs : v ∈ s) : s = {v} := by
    have hcard : s.card ≠ 2 := fun hc => hn ⟨s, hs, hc, hvs⟩
    have hpos := (L.nonempty_of_mem_faces hs).card_pos
    have hle := hdim s hs
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
    rw [hw] at hvs
    simpa only [Finset.mem_singleton.mp hvs] using hw
  let T := hL.toFinset.filter (fun s => v ∉ s)
  let D := ⋃ s ∈ T, convexHull ℝ (s : Set E)
  have hD : IsClosed D :=
    (T.finite_toSet.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hvD : v ∉ D := by
    intro hvD
    obtain ⟨s, hs, hvs⟩ := mem_iUnion₂.mp hvD
    obtain ⟨hsL, hnot⟩ := Finset.mem_filter.mp hs
    exact hnot ((L.vertex_mem_convexHull_iff hv (hL.mem_toFinset.mp hsL)).mp hvs)
  let V : Set L.space := Subtype.val ⁻¹' Dᶜ
  have hV : IsOpen V := hD.isOpen_compl.preimage continuous_subtype_val
  let x : L.space := ⟨v, L.vertices_subset_space hv⟩
  have hsingle : V = {x} := by
    ext y
    constructor
    · intro hy
      obtain ⟨s, hs, hys⟩ := L.mem_space_iff.mp y.property
      have hvs : v ∈ s := by
        by_contra hvnot
        exact hy (mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hL.mem_toFinset.mpr hs, hvnot⟩, hys⟩)
      rw [hsmall s hs hvs, Finset.coe_singleton, convexHull_singleton] at hys
      exact mem_singleton_iff.mpr (Subtype.ext (mem_singleton_iff.mp hys))
    · intro hy
      obtain rfl := mem_singleton_iff.mp hy
      exact hvD
  exact hno x (hsingle ▸ hV)

theorem exists_segment_family_of_vertex_edges
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2)
    (hedge : ∀ v ∈ L.vertices, ∃ s ∈ L.faces, s.card = 2 ∧ v ∈ s) :
    ∃ (I : Type u) (_ : Finite I) (a b : I → E),
      (∀ i, a i ≠ b i) ∧
      L.space = ⋃ i, segment ℝ (a i) (b i) ∧
      ∀ i j, i ≠ j → segment ℝ (a i) (b i) ∩ segment ℝ (a j) (b j) ⊆ {a i, b i} := by
  classical
  let I := {s : Finset E | s ∈ L.faces ∧ s.card = 2}
  have hIfin : Set.Finite {s : Finset E | s ∈ L.faces ∧ s.card = 2} :=
    hL.subset (fun _ hs => hs.1)
  let : Finite I := hIfin.to_subtype
  have hpairs (i : I) : ∃ a b : E, a ≠ b ∧ (i : Finset E) = {a, b} :=
    Finset.card_eq_two.mp i.property.2
  choose a b hab hpair using hpairs
  have hsegment (i : I) : convexHull ℝ (i.val : Set E) = segment ℝ (a i) (b i) := by
    rw [hpair i, Finset.coe_pair, convexHull_pair]
  refine ⟨I, inferInstance, a, b, hab, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
      have hpos := (L.nonempty_of_mem_faces hs).card_pos
      have hle := hdim s hs
      by_cases hc : s.card = 2
      · exact mem_iUnion.mpr ⟨⟨s, hs, hc⟩, (hsegment ⟨s, hs, hc⟩).subset hxs⟩
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
        have hvL : v ∈ L.vertices := by rw [L.mem_vertices, ← hv]; exact hs
        obtain ⟨t, ht, htc, hvt⟩ := hedge v hvL
        rw [hv, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hxs
        subst x
        exact mem_iUnion.mpr ⟨⟨t, ht, htc⟩, (hsegment ⟨t, ht, htc⟩).subset
          (subset_convexHull ℝ (t : Set E) hvt)⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact L.convexHull_subset_space i.property.1 ((hsegment i).symm.subset hi)
  · intro i j hij x hx
    have hxij : x ∈ convexHull ℝ (((i : Finset E) ∩ j : Finset E) : Set E) := by
      rw [Finset.coe_inter, ← L.convexHull_inter_convexHull i.property.1 j.property.1]
      exact ⟨(hsegment i).symm.subset hx.1, (hsegment j).symm.subset hx.2⟩
    have hne : (i : Finset E) ∩ j ≠ i := by
      intro heq
      have hsub : (i : Finset E) ⊆ j := heq ▸ Finset.inter_subset_right
      exact hij (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by
        rw [i.property.2, j.property.2])))
    have hlt := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hne⟩)
    have hpos := (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxij⟩)).card_pos
    have hc : ((i : Finset E) ∩ j).card = 1 := by have := i.property.2; omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
    have hvi : v ∈ (i : Finset E) := Finset.inter_subset_left
      (by rw [hv]; exact Finset.mem_singleton_self v)
    rw [hv, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hxij
    rw [hxij]
    simpa only [hpair i, Finset.mem_insert, Finset.mem_singleton, mem_insert_iff,
      mem_singleton_iff] using hvi

theorem exists_segment_family_of_no_isolated_points
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2)
    (hno : ∀ x : L.space, ¬IsOpen ({x} : Set L.space)) :
    ∃ (I : Type u) (_ : Finite I) (a b : I → E),
      (∀ i, a i ≠ b i) ∧
      L.space = ⋃ i, segment ℝ (a i) (b i) ∧
      ∀ i j, i ≠ j → segment ℝ (a i) (b i) ∩ segment ℝ (a j) (b j) ⊆ {a i, b i} :=
  exists_segment_family_of_vertex_edges L hL hdim
    (vertex_has_edge_of_no_isolated_points L hL hdim hno)

theorem exists_segment_family_of_preperfect
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2) (hacc : Preperfect L.space) :
    ∃ (I : Type u) (_ : Finite I) (a b : I → E),
      (∀ i, a i ≠ b i) ∧
      L.space = ⋃ i, segment ℝ (a i) (b i) ∧
      ∀ i j, i ≠ j → segment ℝ (a i) (b i) ∩ segment ℝ (a j) (b j) ⊆ {a i, b i} := by
  apply exists_segment_family_of_no_isolated_points L hL hdim
  intro x hx
  obtain ⟨U, hU, hUx⟩ := isOpen_induced_iff.mp hx
  have hxU : (x : E) ∈ U := by
    change x ∈ (Subtype.val : L.space → E) ⁻¹' U
    rw [hUx]
    exact mem_singleton x
  obtain ⟨y, hy, hyx⟩ := preperfect_iff_nhds.mp hacc x x.property U (hU.mem_nhds hxU)
  have hy' : (⟨y, hy.2⟩ : L.space) ∈ (Subtype.val : L.space → E) ⁻¹' U := hy.1
  rw [hUx, mem_singleton_iff] at hy'
  exact hyx (congrArg Subtype.val hy')

end PoincareConjecture.M76.PeriodicSquare
