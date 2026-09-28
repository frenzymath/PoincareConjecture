import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineCutOrientation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap











set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}








theorem exists_oriented_affine_height_cut_boxes
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (S : Set E) (A : E →ᵃ[ℝ] ℝ) (c : ℝ)
    (hsection : P.boundary ℝ = S ∩ {x | A x = c})
    (W : Fin (n + 3) → Set E) {R : ℝ} (hR : 0 < R)
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hf : ∀ i, f i 0 = P.edgeCut t i ∧ f i '' box R ⊆ W i ∧
      (∀ x, A (f i x) = c + x.1.1) ∧
      ∀ x ∈ box R, f i x ∈ S ↔ x.2 = 0)
    (hdisj : Pairwise fun i j => Disjoint (f i '' box R) (f j '' box R))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (r : ℝ) (g : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E),
      r ∈ Ioo 0 ε ∧ r ≤ R ∧
      (∀ i,
        (g i = f i ∨ g i = secondReflection.toContinuousAffineEquiv.trans (f i)) ∧
        g i 0 = P.edgeCut t i ∧
        (∀ a, g i '' box a = f i '' box a) ∧
        g i '' box r ⊆ W i ∧
        P.edgeCut t i ∈ interior (g i '' box r) ∧
        (∀ x, A (g i x) = c + x.1.1) ∧
        (∀ x ∈ box r, g i x ∈ S ↔ x.2 = 0) ∧
        ∀ x ∈ box r,
          (g i x ∈ P.cutArc t i ↔ x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) ∧
          (g i x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
            x.1.1 = 0 ∧ x.2 = 0 ∧ x.1.2 ≤ 0)) ∧
      Pairwise fun i j => Disjoint (g i '' box r) (g j '' box r) := by
  classical
  have hlocal (i : Fin (n + 3)) :
      ∃ (g : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (r : ℝ),
        0 < r ∧ r ≤ R ∧
        (g = f i ∨ g = secondReflection.toContinuousAffineEquiv.trans (f i)) ∧
        g 0 = P.edgeCut t i ∧ (∀ a, g '' box a = f i '' box a) ∧
        ∀ x ∈ box r,
          (g x ∈ P.cutArc t i ↔ x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2) ∧
          (g x ∈ P.cutArc t ((finRotate (n + 3)).symm i) ↔
            x.1.1 = 0 ∧ x.2 = 0 ∧ x.1.2 ≤ 0) := by
    apply P.exists_oriented_affine_cut_box hP hinj t ht i (f i) (hf i).1 hR
    intro x hx
    rw [hsection]
    change (f i x ∈ S ∧ A (f i x) = c) ↔ x.1.1 = 0 ∧ x.2 = 0
    rw [(hf i).2.2.2 x hx, (hf i).2.2.1 x]
    constructor
    · rintro ⟨hz, hh⟩
      exact ⟨by linarith, hz⟩
    · rintro ⟨hh, hz⟩
      exact ⟨hz, by rw [hh, add_zero]⟩
  choose g ρ hρ _ hchoice hg0 himage hgerm using hlocal
  obtain ⟨r, hr, hrρ⟩ :=
    (Set.toFinite (univ : Set (Fin (n + 3)))).exists_pos_lt_positive_values
      ρ (lt_min hε hR)
  have hrR : r ≤ R := (hr.2.trans_le (min_le_right _ _)).le
  have hsmall : box r ⊆ box R := by
    rw [box_eq_closedBall, box_eq_closedBall]
    exact Metric.closedBall_subset_closedBall hrR
  have hlocalSmall (i : Fin (n + 3)) : box r ⊆ box (ρ i) := by
    rw [box_eq_closedBall, box_eq_closedBall]
    exact Metric.closedBall_subset_closedBall (hrρ i (mem_univ i) (hρ i)).le
  have hbox (i : Fin (n + 3)) : g i '' box r ⊆ f i '' box R := by
    rw [himage i r]
    exact image_mono hsmall
  refine ⟨r, g, ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩, hrR, ?_, ?_⟩
  · intro i
    refine ⟨hchoice i, hg0 i, himage i, (hbox i).trans (hf i).2.1, ?_, ?_, ?_,
      fun x hx => hgerm i x (hlocalSmall i hx)⟩
    · change P.edgeCut t i ∈ interior ((g i).toHomeomorph '' box r)
      rw [← (g i).toHomeomorph.image_interior]
      exact ⟨0, zero_mem_interior_box hr.1, hg0 i⟩
    · intro x
      rcases hchoice i with h | h
      · rw [h]
        exact (hf i).2.2.1 x
      · rw [h]
        change A (f i (secondReflection x)) = c + x.1.1
        simpa only [secondReflection_apply] using (hf i).2.2.1 (secondReflection x)
    · intro x hx
      rcases hchoice i with h | h
      · rw [h]
        exact (hf i).2.2.2 x (hsmall hx)
      · rw [h]
        change f i (secondReflection x) ∈ S ↔ x.2 = 0
        simpa only [secondReflection_apply] using
          (hf i).2.2.2 (secondReflection x)
            (hsmall ((secondReflection_mem_box r x).mpr hx))
  · intro i j hij
    exact (hdisj hij).mono (hbox i) (hbox j)

end Polygon
