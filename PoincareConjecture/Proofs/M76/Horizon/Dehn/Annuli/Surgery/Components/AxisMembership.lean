import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.LocalInjectivity



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X}
  {S : Set E} {R : Set X} {a b : E}

theorem RawSourceCrossing.mem_double_iff_axis (C : RawSourceCrossing e f S R a b)
    (hR : MapsTo f S R) {x : E} (hx : x ∈ S) (hxT : f x ∈ C.chart.source) :
    x ∈ doubleLocusOn f S ↔ C.chart (f x) 0 = 0 ∧ C.chart (f x) 1 = 0 := by
  have hxB := C.whole_preimage.subset ⟨hx, hxT⟩
  constructor
  · rintro ⟨_, y, hy, hxy, hne⟩
    have hyB := C.whole_preimage.subset ⟨hy, (show f y ∈ C.chart.source from hxy ▸ hxT)⟩
    have hboth : f x ∈ f '' C.left ∧ f x ∈ f '' C.right := by
      rcases hxB with hxL | hxU <;> rcases hyB with hyL | hyU
      · exact (hne (congrArg Subtype.val (C.left_embedding.injective
          (a₁ := ⟨x, hxL⟩) (a₂ := ⟨y, hyL⟩) hxy))).elim
      · exact ⟨⟨x, hxL, rfl⟩, ⟨y, hyU, hxy.symm⟩⟩
      · exact ⟨⟨y, hyL, hxy.symm⟩, ⟨x, hxU, rfl⟩⟩
      · exact (hne (congrArg Subtype.val (C.right_embedding.injective
          (a₁ := ⟨x, hxU⟩) (a₂ := ⟨y, hyU⟩) hxy))).elim
    exact ⟨((C.left_image _ hxT).mp hboth.1).1, ((C.right_image _ hxT).mp hboth.2).1⟩
  · rintro ⟨h0, h1⟩
    obtain ⟨u, hu, hux⟩ := (C.left_image _ hxT).mpr ⟨h0, hR hx⟩
    obtain ⟨v, hv, hvx⟩ := (C.right_image _ hxT).mpr ⟨h1, hR hx⟩
    by_cases hxu : x = u
    · exact ⟨hx, v, C.right_subset hv, hvx.symm,
        fun hxv ↦ disjoint_left.mp C.disjoint hu (hxu ▸ hxv.symm ▸ hv)⟩
    · exact ⟨hx, u, C.left_subset hu, hux.symm, hxu⟩

theorem RawSourceCrossing.branch_mapsTo_chart (C : RawSourceCrossing e f S R a b)
    (side : Bool) : MapsTo f (if side then C.right else C.left) C.chart.source := by
  intro x hx
  apply (C.whole_preimage.symm.subset ?_).2
  cases side
  · exact Or.inl hx
  · exact Or.inr hx

theorem RawSourceCrossing.branch_axis_surjective (C : RawSourceCrossing e f S R a b)
    (side : Bool) {z : Fin 3 → ℝ} (hz : z ∈ C.chart.target)
    (h0 : z 0 = 0) (h1 : z 1 = 0) (hR : C.chart.symm z ∈ R) :
    ∃ x ∈ (if side then C.right else C.left), C.chart (f x) = z := by
  have hsrc := C.chart.map_target hz
  have hi := C.chart.right_inv hz
  have him : C.chart.symm z ∈ f '' (if side then C.right else C.left) := by
    cases side
    · exact (C.left_image _ hsrc).mpr ⟨by rw [hi]; exact h0, hR⟩
    · exact (C.right_image _ hsrc).mpr ⟨by rw [hi]; exact h1, hR⟩
  obtain ⟨x, hx, hfx⟩ := him
  exact ⟨x, hx, (congrArg C.chart hfx).trans hi⟩

end PoincareConjecture.M76.Dehn.Annuli
