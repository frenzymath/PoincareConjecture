import PoincareConjecture.Proofs.M76.Mathlib.SegmentStripProduct

set_option autoImplicit false

open Set Geometry AffineMap PLStrip

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_segment_collar {S : Set E} {e : square ≃ₜ S}
    (he : e.IsFinitePL) (A : E → ℝ) {l r : E} (hlr : l ≠ r)
    {α β : ℝ} (hαβ : α < β) (L R : ℝ → E)
    (hheight : ∀ p : square, A (e p) = α + (β - α) * (p : ℝ × ℝ).2)
    (hbase : ∀ (s : ℝ) (hs : s ∈ Icc 0 1),
      (e ⟨(s, 0), ⟨hs, ⟨le_rfl, zero_le_one⟩⟩⟩ : E) = lineMap l r s)
    (hside : ∀ (t : ℝ) (ht : t ∈ Icc 0 1),
      (e ⟨(0, t), ⟨⟨le_rfl, zero_le_one⟩, ht⟩⟩ : E) = L (α + (β - α) * t) ∧
      (e ⟨(1, t), ⟨⟨zero_le_one, le_rfl⟩, ht⟩⟩ : E) = R (α + (β - α) * t)) :
    ∃ H : (segment ℝ l r ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ S,
      H.IsFinitePL ∧
      (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ segment ℝ l r),
        (H ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = x) ∧
      ∀ (t : ℝ) (ht : t ∈ Icc α β),
        (H ⟨(l, t), ⟨left_mem_segment ℝ l r, ht⟩⟩ : E) = L t ∧
        (H ⟨(r, t), ⟨right_mem_segment ℝ l r, ht⟩⟩ : E) = R t := by
  obtain ⟨f, hf, hfval⟩ := exists_segmentProduct_homeomorph hlr hαβ
  let H := f.symm.trans e
  refine ⟨H, hf.symm.trans he, ?_, ?_, ?_⟩
  · intro p
    have hp := hfval (f.symm p)
    rw [f.apply_symm_apply] at hp
    change A (e (f.symm p)) = (p : E × ℝ).2
    rw [hheight]
    exact (congrArg Prod.snd hp).symm
  · intro x hx
    let p : (segment ℝ l r ×ˢ Icc α β : Set (E × ℝ)) :=
      ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩
    have hp := hfval (f.symm p)
    rw [f.apply_symm_apply] at hp
    have hp0 : ((f.symm p : square) : ℝ × ℝ).2 = 0 := by
      have ht := congrArg Prod.snd hp
      change α = α + (β - α) * ((f.symm p : square) : ℝ × ℝ).2 at ht
      have hz : (β - α) * ((f.symm p : square) : ℝ × ℝ).2 = 0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hαβ.ne')
    have hpeq : f.symm p =
        ⟨(((f.symm p : square) : ℝ × ℝ).1, 0),
          ⟨(f.symm p).property.1, ⟨le_rfl, zero_le_one⟩⟩⟩ :=
      Subtype.ext (Prod.ext rfl hp0)
    change (e (f.symm p) : E) = x
    rw [hpeq, hbase _ (f.symm p).property.1]
    exact (congrArg Prod.fst hp).symm
  · intro t ht
    let z := (t - α) / (β - α)
    have hz : z ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hαβ).le,
        (div_le_one (sub_pos.mpr hαβ)).mpr (sub_le_sub_right ht.2 α)⟩
    have hzt : α + (β - α) * z = t := by
      dsimp only [z]
      field_simp [sub_ne_zero.mpr hαβ.ne']
      ring
    constructor
    · let q : square := ⟨(0, z), ⟨⟨le_rfl, zero_le_one⟩, hz⟩⟩
      have hq : f q = ⟨(l, t), ⟨left_mem_segment ℝ l r, ht⟩⟩ := by
        apply Subtype.ext
        rw [hfval]
        change (lineMap l r 0, α + (β - α) * z) = (l, t)
        rw [lineMap_apply_zero, hzt]
      change (e (f.symm _) : E) = L t
      rw [← hq, f.symm_apply_apply]
      exact (hside z hz).1.trans (congrArg L hzt)
    · let q : square := ⟨(1, z), ⟨⟨zero_le_one, le_rfl⟩, hz⟩⟩
      have hq : f q = ⟨(r, t), ⟨right_mem_segment ℝ l r, ht⟩⟩ := by
        apply Subtype.ext
        rw [hfval]
        change (lineMap l r 1, α + (β - α) * z) = (r, t)
        rw [lineMap_apply_one, hzt]
      change (e (f.symm _) : E) = R t
      rw [← hq, f.symm_apply_apply]
      exact (hside z hz).2.trans (congrArg R hzt)

end Homeomorph
