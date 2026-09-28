import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.ConnectedSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.SectorConnectivity








set_option autoImplicit false
open Set Filter
open scoped Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

variable {X : Type*} [TopologicalSpace X]


theorem support_eventuallyEq_closure {A B : Set X} {q : X}
    (h : A =ᶠ[𝓝 q] B) : closure A =ᶠ[𝓝 q] closure B := by
  obtain ⟨U, hU, hUo, hqU⟩ := mem_nhds_iff.mp h
  filter_upwards [hUo.mem_nhds hqU] with z hz
  apply propext
  constructor
  · intro ha
    apply closure_mono (show U ∩ A ⊆ B from fun x hx =>
      (propext_iff.mp (hU hx.1)).mp hx.2)
    exact hUo.inter_closure ⟨hz, ha⟩
  · intro hb
    apply closure_mono (show U ∩ B ⊆ A from fun x hx =>
      (propext_iff.mp (hU hx.1)).mpr hx.2)
    exact hUo.inter_closure ⟨hz, hb⟩



theorem closed_support_germ_eq_closure_region {K A U : Set X}
    (hK : IsClosed K) (hregular : closure (interior K) = K)
    (hU : IsOpen U) (hA : A ⊆ K) (hinterior : U ∩ interior K ⊆ A)
    {q : X} (hq : q ∈ U) : K =ᶠ[𝓝 q] closure A := by
  filter_upwards [hU.mem_nhds hq] with z hz
  apply propext
  constructor
  · intro hk
    apply closure_mono hinterior
    exact hU.inter_closure ⟨hz, hregular.symm ▸ hk⟩
  · exact fun hz => closure_minimal hA hK hz



theorem closed_regular_support_germ_of_two_regions {K U A B : Set X}
    (hK : IsClosed K) (hregular : closure (interior K) = K)
    (hU : IsOpen U) (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hboundary : ∀ z ∈ U, z ∈ frontier K ↔ z ∉ A ∪ B)
    {q : X} (hqU : q ∈ U) (hq : q ∈ frontier K) :
    K =ᶠ[𝓝 q] closure A ∨ K =ᶠ[𝓝 q] closure B := by
  have hdA : Disjoint A (frontier K) := disjoint_left.mpr fun z hz hf =>
    (hboundary z (hAU hz)).mp hf (Or.inl hz)
  have hdB : Disjoint B (frontier K) := disjoint_left.mpr fun z hz hf =>
    (hboundary z (hBU hz)).mp hf (Or.inr hz)
  have hinterior : U ∩ interior K ⊆ A ∪ B := by
    intro z hz
    by_contra hn
    exact ((hboundary z hz.1).mpr hn).2 hz.2
  rcases preconnected_subset_interior_or_compl_of_disjoint_frontier hA hK hdA with ha | ha
  · rcases preconnected_subset_interior_or_compl_of_disjoint_frontier hB hK hdB with hb | hb
    · have hUK : U ⊆ K := by
        intro z hz
        by_cases hf : z ∈ frontier K
        · exact hK.closure_eq ▸ hf.1
        · have hs : z ∈ A ∪ B := by
            by_contra hn
            exact hf ((hboundary z hz).mpr hn)
          exact interior_subset (hs.elim (fun h => ha h) (fun h => hb h))
      exact False.elim (hq.2 (hU.subset_interior_iff.mpr hUK hqU))
    · apply Or.inl
      apply closed_support_germ_eq_closure_region hK hregular hU
        (fun _ h => interior_subset (ha h)) _ hqU
      intro z hz
      exact (hinterior hz).resolve_right (fun h => hb h (interior_subset hz.2))
  · rcases preconnected_subset_interior_or_compl_of_disjoint_frontier hB hK hdB with hb | hb
    · apply Or.inr
      apply closed_support_germ_eq_closure_region hK hregular hU
        (fun _ h => interior_subset (hb h)) _ hqU
      intro z hz
      exact (hinterior hz).resolve_left (fun h => ha h (interior_subset hz.2))
    · have hempty : U ∩ interior K ⊆ (∅ : Set X) := by
        intro z hz
        exact False.elim ((hinterior hz).elim
          (fun h => ha h (interior_subset hz.2)) (fun h => hb h (interior_subset hz.2)))
      have hqK : q ∈ K := hK.closure_eq ▸ hq.1
      have hqcl : q ∈ closure (∅ : Set X) :=
        closure_mono hempty (hU.inter_closure ⟨hqU, hregular.symm ▸ hqK⟩)
      simp only [closure_empty, mem_empty_iff_false] at hqcl



theorem closed_regular_support_germ_of_two_rays
    (c : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (hK : IsClosed K) (hregular : closure (interior K) = K)
    (hq : c 0 ∈ frontier K)
    (hfront : frontier K =ᶠ[𝓝 (c 0)]
      {z | (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0)}) :
    (K =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) ∨
      (K =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) := by
  obtain ⟨r, hr, hbox⟩ := exists_pos_coordinate_box_subset c hfront
  let A := coordinateBox c r ∩ {z | 0 < c.coord 1 z ∧ 0 < c.coord 2 z}
  let B := coordinateBox c r ∩ {z | c.coord 1 z < 0 ∨ c.coord 2 z < 0}
  have hboundary : ∀ z ∈ coordinateBox c r,
      z ∈ frontier K ↔ z ∉ A ∪ B := by
    intro z hz
    change frontier K z ↔ _
    rw [propext_iff.mp (hbox hz)]
    simp only [A, B, mem_ofPred_eq, mem_union, mem_inter_iff, hz, true_and,
      not_or, not_and_or, not_lt]
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · exact ⟨Or.inl hx.le, hx.ge, hy⟩
      · exact ⟨Or.inr hy.le, hx, hy.ge⟩
    · rintro ⟨hx | hy, hx', hy'⟩
      · exact Or.inl ⟨le_antisymm hx hx', hy'⟩
      · exact Or.inr ⟨hx', le_antisymm hy hy'⟩
  have hA : closure A =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
    rw [← closure_positiveSector c]
    apply support_eventuallyEq_closure
    filter_upwards [coordinateBox_mem_nhds c hr] with z hz
    exact propext (and_iff_right hz)
  have hB : closure B =ᶠ[𝓝 (c 0)]
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
    rw [← closure_openReflexSector c]
    apply support_eventuallyEq_closure
    filter_upwards [coordinateBox_mem_nhds c hr] with z hz
    exact propext (and_iff_right hz)
  rcases closed_regular_support_germ_of_two_regions hK hregular
    (isOpen_coordinateBox c r) inter_subset_left inter_subset_left
    (coordinateBox_positive_isPreconnected c r) (coordinateBox_reflex_isPreconnected c hr)
    hboundary (vertex_mem_coordinateBox c hr) hq with h | h
  · exact Or.inl (h.trans hA)
  · exact Or.inr (h.trans hB)



theorem closed_regular_support_germ_of_line
    (c : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (hK : IsClosed K) (hregular : closure (interior K) = K)
    (hq : c 0 ∈ frontier K)
    (hfront : frontier K =ᶠ[𝓝 (c 0)] {z | c.coord 1 z = 0}) :
    (K =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z}) ∨
      (K =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0}) := by
  obtain ⟨r, hr, hbox⟩ := exists_pos_coordinate_box_subset c hfront
  let A := coordinateBox c r ∩ {z | 0 < c.coord 1 z}
  let B := coordinateBox c r ∩ {z | c.coord 1 z < 0}
  have hboundary : ∀ z ∈ coordinateBox c r,
      z ∈ frontier K ↔ z ∉ A ∪ B := by
    intro z hz
    change frontier K z ↔ _
    rw [propext_iff.mp (hbox hz)]
    simp only [A, B, mem_ofPred_eq, mem_union, mem_inter_iff, hz, true_and,
      not_or, not_lt]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  have hA : closure A =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z} := by
    rw [← closure_positiveHalfspace c]
    apply support_eventuallyEq_closure
    filter_upwards [coordinateBox_mem_nhds c hr] with z hz
    exact propext (and_iff_right hz)
  have hB : closure B =ᶠ[𝓝 (c 0)] {z | c.coord 1 z ≤ 0} := by
    rw [← closure_negativeHalfspace c]
    apply support_eventuallyEq_closure
    filter_upwards [coordinateBox_mem_nhds c hr] with z hz
    exact propext (and_iff_right hz)
  rcases closed_regular_support_germ_of_two_regions hK hregular
    (isOpen_coordinateBox c r) inter_subset_left inter_subset_left
    (coordinateBox_positiveHalfspace_isPreconnected c r)
    (coordinateBox_negativeHalfspace_isPreconnected c r)
    hboundary (vertex_mem_coordinateBox c hr) hq with h | h
  · exact Or.inl (h.trans hA)
  · exact Or.inr (h.trans hB)

end PoincareConjecture.Topology.Surface
