import PoincareConjecture.Proofs.M76.Mathlib.RegularApexTriangleStrip
import PoincareConjecture.Proofs.M76.Mathlib.PLSquareReflection
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevelUniqueness

set_option autoImplicit false

open Set Geometry PLStrip

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_upper_triangle_strip (A : E →ᵃ[ℝ] ℝ) {v u w : E} {α β : ℝ}
    (hi : AffineIndependent ℝ ![v, u, w])
    (hv : β < A v) (hαβ : α < β) (hu : A u < α) (hw : A w < α) :
    ∃ e : square ≃ₜ (convexHull ℝ (insert v ({u, w} : Set E)) ∩
        {x | A x ∈ Icc α β} : Set E),
      e.IsFinitePL ∧
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
  obtain ⟨e, he, _, hheight, hside, hends⟩ := (-A).exists_lower_triangle_strip hi
    (neg_lt_neg hv) (neg_lt_neg hαβ) (neg_lt_neg hu) (neg_lt_neg hw)
  have hset : (convexHull ℝ (insert v ({u, w} : Set E)) ∩
        {x | (-A) x ∈ Icc (-β) (-α)}) =
      convexHull ℝ (insert v ({u, w} : Set E)) ∩ {x | A x ∈ Icc α β} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, coe_neg, Pi.neg_apply, neg_le_neg_iff]
    tauto
  let g := (flipHeight.trans e).trans (Homeomorph.setCongr hset)
  have hg : g.IsFinitePL := by
    obtain ⟨f, hf, hfe⟩ := isFinitePL_flipHeight.trans he
    exact ⟨f, hf, fun p => hfe p⟩
  have huu : A u ≠ A v := ne_of_lt (hu.trans (hαβ.trans hv))
  have hww : A w ≠ A v := ne_of_lt (hw.trans (hαβ.trans hv))
  have hflip (s t : ℝ) (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1)
      (ht' : 1 - t ∈ Icc (0 : ℝ) 1) :
      flipHeight ⟨(s, t), ⟨hs, ht⟩⟩ = ⟨(s, 1 - t), ⟨hs, ht'⟩⟩ := rfl
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro p
    have ht := hheight (flipHeight p)
    change -A (e (flipHeight p)) = -β + (-α - -β) * (1 - (p : ℝ × ℝ).2) at ht
    change A (e (flipHeight p)) = α + (β - α) * (p : ℝ × ℝ).2
    nlinarith [ht]
  · intro t ht
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hc : -β + (-α - -β) * (1 - t) = -(α + (β - α) * t) := by ring
    constructor
    · change (e (flipHeight ⟨(0, t), _⟩) : E) = _
      rw [hflip 0 t ⟨le_rfl, zero_le_one⟩ ht ht', (hside (1 - t) ht').1,
        hc, A.edgeLevel_neg huu]
    · change (e (flipHeight ⟨(1, t), _⟩) : E) = _
      rw [hflip 1 t ⟨zero_le_one, le_rfl⟩ ht ht', (hside (1 - t) ht').2,
        hc, A.edgeLevel_neg hww]
  · intro s hs
    constructor
    · change (e (flipHeight ⟨(s, 0), _⟩) : E) = _
      have hf : flipHeight ⟨(s, 0), ⟨hs, ⟨le_rfl, zero_le_one⟩⟩⟩ =
          ⟨(s, 1), ⟨hs, ⟨zero_le_one, le_rfl⟩⟩⟩ := by
        apply Subtype.ext
        simp [flipHeight]
      rw [hf, (hends s hs).2, A.edgeLevel_neg huu, A.edgeLevel_neg hww]
    · change (e (flipHeight ⟨(s, 1), _⟩) : E) = _
      have hf : flipHeight ⟨(s, 1), ⟨hs, ⟨zero_le_one, le_rfl⟩⟩⟩ =
          ⟨(s, 0), ⟨hs, ⟨le_rfl, zero_le_one⟩⟩⟩ := by
        apply Subtype.ext
        simp [flipHeight]
      rw [hf, (hends s hs).1, A.edgeLevel_neg huu, A.edgeLevel_neg hww]

end AffineMap
