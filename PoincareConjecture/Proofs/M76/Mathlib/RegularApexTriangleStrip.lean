import PoincareConjecture.Proofs.M76.Mathlib.RegularApexStripCoordinates

set_option autoImplicit false

open Set Geometry PLStrip

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem apexStrip_image_eq_slab (A : E →ᵃ[ℝ] ℝ) {v u w : E} {α β : ℝ}
    (hv : A v < α) (hαβ : α < β) (hu : β < A u) (hw : β < A w) :
    (A.apexStripCoordinates v u w α β ∘ stripMap (β - A v) (α - A v)) '' square =
      convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x ∈ Icc α β} := by
  rw [affine_strip_image (sub_pos.mpr (hv.trans hαβ)) (sub_pos.mpr hv)]
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    rw [apexStripCoordinates_left, apexStripCoordinates_right] at hx
    have hc : α + (β - α) * t ∈ Icc α β := by
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hαβ.le) ht.1,
        mul_nonneg (sub_nonneg.mpr hαβ.le) (sub_nonneg.mpr ht.2)]
    rw [← A.triangle_section_eq_edgeLevels (hv.trans_le hc.1)
      (hc.2.trans_lt hu) (hc.2.trans_lt hw)] at hx
    refine ⟨hx.1, ?_⟩
    change A x ∈ Icc α β
    rwa [hx.2]
  · rintro ⟨hx, hAx⟩
    let t := (A x - α) / (β - α)
    have ht : t ∈ Icc 0 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hAx.1) (sub_pos.mpr hαβ).le,
        (div_le_one (sub_pos.mpr hαβ)).mpr (sub_le_sub_right hAx.2 α)⟩
    have hc : α + (β - α) * t = A x := by
      dsimp only [t]
      field_simp [sub_ne_zero.mpr hαβ.ne']
      ring
    refine ⟨t, ht, ?_⟩
    rw [apexStripCoordinates_left, apexStripCoordinates_right, hc,
      ← A.triangle_section_eq_edgeLevels (hv.trans_le hAx.1)
        (hAx.2.trans_lt hu) (hAx.2.trans_lt hw)]
    exact ⟨hx, rfl⟩

theorem exists_lower_triangle_strip (A : E →ᵃ[ℝ] ℝ) {v u w : E} {α β : ℝ}
    (hi : AffineIndependent ℝ ![v, u, w])
    (hv : A v < α) (hαβ : α < β) (hu : β < A u) (hw : β < A w) :
    ∃ e : square ≃ₜ (convexHull ℝ (insert v ({u, w} : Set E)) ∩
        {x | A x ∈ Icc α β} : Set E),
      e.IsFinitePL ∧
      (∀ p : square, (e p : E) = A.apexStripCoordinates v u w α β
        (stripMap (β - A v) (α - A v) p)) ∧
      (∀ p : square, A (e p) = α + (β - α) * (p : ℝ × ℝ).2) ∧
      (∀ (t : ℝ) (ht : t ∈ Icc 0 1),
        (e ⟨(0, t), ⟨⟨le_rfl, zero_le_one⟩, ht⟩⟩ : E) =
          A.edgeLevel v u (α + (β - α) * t) ∧
        (e ⟨(1, t), ⟨⟨zero_le_one, le_rfl⟩, ht⟩⟩ : E) =
          A.edgeLevel v w (α + (β - α) * t)) ∧
      ∀ (s : ℝ) (hs : s ∈ Icc 0 1),
        (e ⟨(s, 0), ⟨hs, ⟨le_rfl, zero_le_one⟩⟩⟩ : E) =
          lineMap (A.edgeLevel v u α) (A.edgeLevel v w α) s ∧
        (e ⟨(s, 1), ⟨hs, ⟨zero_le_one, le_rfl⟩⟩⟩ : E) =
          lineMap (A.edgeLevel v u β) (A.edgeLevel v w β) s := by
  have huu : A u ≠ A v := ne_of_gt (hv.trans (hαβ.trans hu))
  have hww : A w ≠ A v := ne_of_gt (hv.trans (hαβ.trans hw))
  have hex := exists_affine_strip_homeomorph
    (sub_pos.mpr (hv.trans hαβ)) (sub_pos.mpr hv)
    (A.apexStripCoordinates v u w α β) (A.apexStripCoordinates_injective hi huu hww hαβ.ne)
  rw [A.apexStrip_image_eq_slab hv hαβ hu hw] at hex
  obtain ⟨e, he, heval⟩ := hex
  refine ⟨e, he, heval, ?_, ?_, ?_⟩
  · intro p
    rw [heval, A.apply_apexStripCoordinates huu hww]
    rfl
  · intro t ht
    constructor
    · rw [heval, stripMap_left _ _ ht.1, apexStripCoordinates_left]
    · rw [heval, stripMap_right _ _ ht.2, apexStripCoordinates_right]
  · intro s hs
    constructor
    · rw [heval, stripMap_bottom _ _ hs.1, apexStripCoordinates_apply,
        edgeLevel, edgeLevel, lineMap_apply_module']
      module
    · rw [heval, stripMap_top _ _ hs.2, apexStripCoordinates_apply,
        edgeLevel, edgeLevel, lineMap_apply_module']
      module

end AffineMap
