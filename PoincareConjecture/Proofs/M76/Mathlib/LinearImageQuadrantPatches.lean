import PoincareConjecture.Proofs.M76.Mathlib.SourcePoleQuadrantPatches
import PoincareConjecture.Proofs.M76.Mathlib.LinearPatchHomeomorphisms
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateFourRegionIncidence












set_option autoImplicit false

open Set Geometry RectangleCornerArcs CoordinateFourRegions

namespace CoordinateFourRegions

private theorem weakSign_of_mem_zero_uIcc {i : Bool} {a x : ℝ}
    (ha : weakSign i a) (hx : x ∈ uIcc 0 a) : weakSign i x := by
  cases i
  · rw [uIcc_of_le ha] at hx
    exact hx.1
  · rw [uIcc_of_ge ha] at hx
    exact hx.2

end CoordinateFourRegions

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





structure LinearImageQuadrantData (ψ : (ℝ × ℝ) → E)
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)) (F : Set ((ℝ × ℝ) × ℝ))
    (p : E) (t z : ℝ) (i : Bool × Bool) : Prop where
  disk : IsFinitePLBallPair (ℝ × ℝ) (e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)))
    ((e '' (ψ '' cornerArc 0 t 0 z)) ∪ (e '' (ψ '' cornerArc t 0 z 0)))
  inner : IsFinitePLBallPair ℝ (e '' (ψ '' cornerArc 0 t 0 z))
    {e (ψ (0, z)), e (ψ (t, 0))}
  outer : IsFinitePLBallPair ℝ (e '' (ψ '' cornerArc t 0 z 0))
    {e (ψ (0, z)), e (ψ (t, 0))}
  vertical : IsFinitePLBallPair ℝ (e '' (ψ '' ({0} ×ˢ uIcc 0 z)))
    {e p, e (ψ (0, z))}
  horizontal : IsFinitePLBallPair ℝ (e '' (ψ '' (uIcc 0 t ×ˢ {0})))
    {e p, e (ψ (t, 0))}
  disk_PL : (e.toHomeomorph.image (ψ '' (uIcc 0 t ×ˢ uIcc 0 z))).IsFinitePL
  inner_PL : (e.toHomeomorph.image (ψ '' cornerArc 0 t 0 z)).IsFinitePL
  outer_PL : (e.toHomeomorph.image (ψ '' cornerArc t 0 z 0)).IsFinitePL
  vertical_PL : (e.toHomeomorph.image (ψ '' ({0} ×ˢ uIcc 0 z))).IsFinitePL
  horizontal_PL : (e.toHomeomorph.image (ψ '' (uIcc 0 t ×ˢ {0}))).IsFinitePL
  region_subset : e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ⊆ region F i
  vertical_arc : e '' (ψ '' ({0} ×ˢ uIcc 0 z)) ⊆ arc F (false, i.2)
  horizontal_arc : e '' (ψ '' (uIcc 0 t ×ˢ {0})) ⊆ arc F (true, i.1)
  graph_contact : (e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z))) ∩ graph F =
    e '' (ψ '' cornerArc 0 t 0 z)
  inner_rim : e '' (ψ '' cornerArc 0 t 0 z) ⊆ arc F (false, i.2) ∪ arc F (true, i.1)
  outer_proper : (e '' (ψ '' cornerArc t 0 z 0)) \ {e (ψ (0, z)), e (ψ (t, 0))} ⊆
    region F i \ (arc F (false, i.2) ∪ arc F (true, i.1))







theorem SourcePoleQuadrantData.linear_image_coordinate_attachment
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} {p q : E} {A : E →ₗ[ℝ] ℝ}
    {t z : ℝ} (h : SourcePoleQuadrantData ψ F S g p q A t z)
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)) (T : Set ((ℝ × ℝ) × ℝ))
    (hfirst : ∀ x : ℝ × ℝ, (e (ψ x)).1.1 = x.1)
    (hlast : ∀ x : ℝ × ℝ, (e (ψ x)).2 = x.2)
    (hfront : e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ⊆ T)
    (i : Bool × Bool) (ht : weakSign i.1 t) (hz : weakSign i.2 z) :
    LinearImageQuadrantData ψ e T p t z i := by
  obtain ⟨hd, hdPL, _, _, _⟩ := h.disk.linear_image_patch_data e
  obtain ⟨hu, huPL, _, _, _⟩ := h.inner.linear_image_patch_data e
  obtain ⟨hw, hwPL, _, _, _⟩ := h.outer.linear_image_patch_data e
  obtain ⟨hv, hvPL, _, _, _⟩ := h.vertical.linear_image_patch_data e
  obtain ⟨hh, hhPL, _, _, _⟩ := h.horizontal.linear_image_patch_data e
  have hF (x : ℝ × ℝ) (hx : x ∈ uIcc 0 t ×ˢ uIcc 0 z) : e (ψ x) ∈ T :=
    hfront ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩
  have hregion : e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ⊆ region T i := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨hF x hx, ?_, ?_⟩
    · change weakSign i.1 (e (ψ x)).1.1
      rw [hfirst]
      exact weakSign_of_mem_zero_uIcc ht hx.1
    · change weakSign i.2 (e (ψ x)).2
      rw [hlast]
      exact weakSign_of_mem_zero_uIcc hz hx.2
  have hvArc : e '' (ψ '' ({0} ×ˢ uIcc 0 z)) ⊆ arc T (false, i.2) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxR : x ∈ uIcc 0 t ×ˢ uIcc 0 z := ⟨hx.1 ▸ left_mem_uIcc, hx.2⟩
    refine ⟨hF x hxR, (hfirst x).trans hx.1, ?_⟩
    change weakSign i.2 (e (ψ x)).2
    rw [hlast]
    exact weakSign_of_mem_zero_uIcc hz hx.2
  have hhArc : e '' (ψ '' (uIcc 0 t ×ˢ {0})) ⊆ arc T (true, i.1) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxR : x ∈ uIcc 0 t ×ˢ uIcc 0 z := ⟨hx.1, hx.2 ▸ left_mem_uIcc⟩
    refine ⟨hF x hxR, (hlast x).trans hx.2, ?_⟩
    change weakSign i.1 (e (ψ x)).1.1
    rw [hfirst]
    exact weakSign_of_mem_zero_uIcc ht hx.1
  have hcontact : (e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z))) ∩ graph T =
      e '' (ψ '' cornerArc 0 t 0 z) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, hxg⟩
      refine ⟨ψ x, ⟨x, ?_, rfl⟩, rfl⟩
      rcases hxg.2 with hxzero | hxzero
      · exact Or.inl ⟨(hfirst x).symm.trans hxzero, hx.2⟩
      · exact Or.inr ⟨hx.1, (hlast x).symm.trans hxzero⟩
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hxR := cornerArc_subset_rectangle 0 t 0 z hx
      refine ⟨⟨ψ x, ⟨x, hxR, rfl⟩, rfl⟩, hF x hxR, ?_⟩
      rcases hx with hx | hx
      · exact Or.inl ((hfirst x).trans hx.1)
      · exact Or.inr ((hlast x).trans hx.2)
  have hwD : e '' (ψ '' cornerArc t 0 z 0) ⊆ e '' (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) :=
    image_mono (fun x hx => h.disk.1 (Or.inr hx))
  have huw : (e '' (ψ '' cornerArc 0 t 0 z)) ∩ (e '' (ψ '' cornerArc t 0 z 0)) =
      {e (ψ (0, z)), e (ψ (t, 0))} := by
    rw [← image_inter e.injective, h.corner_inter, image_pair]
  refine {
    disk := by simpa only [image_union] using hd
    inner := by simpa only [image_pair] using hu
    outer := by simpa only [image_pair] using hw
    vertical := by simpa only [image_pair] using hv
    horizontal := by simpa only [image_pair] using hh
    disk_PL := hdPL
    inner_PL := huPL
    outer_PL := hwPL
    vertical_PL := hvPL
    horizontal_PL := hhPL
    region_subset := hregion
    vertical_arc := hvArc
    horizontal_arc := hhArc
    graph_contact := hcontact
    inner_rim := ?_
    outer_proper := ?_ }
  · intro x hx
    have hxcontact := hcontact.symm.subset hx
    exact (region_inter_graph T i).subset ⟨hregion hxcontact.1, hxcontact.2⟩
  · intro x hx
    refine ⟨hregion (hwD hx.1), ?_⟩
    intro hxrim
    have hxg := ((region_inter_graph T i).symm.subset hxrim).2
    exact hx.2 (huw.subset ⟨hcontact.subset ⟨hwD hx.1, hxg⟩, hx.1⟩)

end Geometry
