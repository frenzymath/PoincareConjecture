import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachmentContinuity



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem commonCollarAttachment_end
    {E X Z : Type*} (c : E × ℝ → X) (rim : Bool → Z → E)
    (G : X → X) (f : ℝ × Z → X) (a : ℝ) (b : Bool) (z : Z) :
    commonCollarAttachment c rim G f a (if b then 2 else -2, z) = c (rim b z, 0) := by
  cases b <;> norm_num [commonCollarAttachment]

theorem commonCollarAttachment_mapsTo
    {E X Z : Type*} (c : E × ℝ → X) (rim : Bool → Z → E)
    {K : Set E} {A : Set Z} {R : Set X} {a : ℝ} (ha : 0 < a)
    (hc : MapsTo c (K ×ˢ Icc (0 : ℝ) a) R)
    (hrim : ∀ b, MapsTo (rim b) A K)
    (G : X → X) (f : ℝ × Z → X)
    (hG : MapsTo (G ∘ f) (Icc (-1 : ℝ) 1 ×ˢ A) R) :
    MapsTo (commonCollarAttachment c rim G f a) (Icc (-2 : ℝ) 2 ×ˢ A) R := by
  intro z hz
  unfold commonCollarAttachment
  split_ifs with hl hu
  · apply hc
    exact ⟨hrim false hz.2, by nlinarith [hz.1.1], by nlinarith⟩
  · apply hc
    exact ⟨hrim true hz.2, by nlinarith [hz.1.2], by nlinarith⟩
  · exact hG ⟨⟨(lt_of_not_ge hl).le, (lt_of_not_ge hu).le⟩, hz.2⟩

theorem commonCollarAttachment_boundary_iff
    {E X Z : Type*} (c : E × ℝ → X) (rim : Bool → Z → E)
    {K : Set E} {A : Set Z} {B : Set X} {a : ℝ} (ha : 0 < a)
    (hc : ∀ z ∈ K ×ˢ Icc (0 : ℝ) a, c z ∈ B ↔ z.2 = 0)
    (hrim : ∀ b, MapsTo (rim b) A K)
    (G : X → X) (f : ℝ × Z → X)
    (hG : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ A, G (f z) ∉ B)
    {z : ℝ × Z} (hz : z ∈ Icc (-2 : ℝ) 2 ×ˢ A) :
    commonCollarAttachment c rim G f a z ∈ B ↔ z.1 = -2 ∨ z.1 = 2 := by
  unfold commonCollarAttachment
  split_ifs with hl hu
  · rw [hc _ ⟨hrim false hz.2, by nlinarith [hz.1.1], by nlinarith⟩]
    constructor
    · intro h
      exact Or.inl (by nlinarith)
    · rintro (h | h)
      · rw [h]; ring
      · linarith
  · rw [hc _ ⟨hrim true hz.2, by nlinarith [hz.1.2], by nlinarith⟩]
    constructor
    · intro h
      exact Or.inr (by nlinarith)
    · rintro (h | h)
      · linarith
      · rw [h]; ring
  · have hnot := hG z ⟨⟨(lt_of_not_ge hl).le, (lt_of_not_ge hu).le⟩, hz.2⟩
    constructor
    · exact fun h => (hnot h).elim
    · rintro (h | h) <;> linarith

theorem commonCollarAttachment_image_in_open_strip
    {E X Z : Type*} (c : E × ℝ → X) (rim : Bool → Z → E)
    {K : Set E} {A : Set Z} {a : ℝ} (ha : 0 < a)
    (hc : InjOn c (K ×ˢ Icc (0 : ℝ) a))
    (hrim : ∀ b, MapsTo (rim b) A K)
    (G : X → X) (f : ℝ × Z → X)
    (hgap : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ A, G (f z) ∉ c '' (K ×ˢ Ico (0 : ℝ) a)) :
    (commonCollarAttachment c rim G f a '' (Icc (-2 : ℝ) 2 ×ˢ A)) ∩
        (c '' (K ×ˢ Ico (0 : ℝ) a)) =
      c '' (((rim false '' A) ∪ (rim true '' A)) ×ˢ Ico (0 : ℝ) a) := by
  ext x
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, w, hw, heq⟩
    unfold commonCollarAttachment at heq ⊢
    split_ifs at heq ⊢ with hl hu
    · have hp : (rim false z.2, a * (z.1 + 2)) ∈ K ×ˢ Icc (0 : ℝ) a :=
        ⟨hrim false hz.2, by nlinarith [hz.1.1], by nlinarith⟩
      have hh := hc ⟨hw.1, hw.2.1, hw.2.2.le⟩ hp heq
      refine ⟨(rim false z.2, a * (z.1 + 2)), ⟨Or.inl ⟨z.2, hz.2, rfl⟩, ?_⟩, rfl⟩
      exact hh ▸ hw.2
    · have hp : (rim true z.2, a * (2 - z.1)) ∈ K ×ˢ Icc (0 : ℝ) a :=
        ⟨hrim true hz.2, by nlinarith [hz.1.2], by nlinarith⟩
      have hh := hc ⟨hw.1, hw.2.1, hw.2.2.le⟩ hp heq
      refine ⟨(rim true z.2, a * (2 - z.1)), ⟨Or.inr ⟨z.2, hz.2, rfl⟩, ?_⟩, rfl⟩
      exact hh ▸ hw.2
    · exact (hgap z ⟨⟨(lt_of_not_ge hl).le, (lt_of_not_ge hu).le⟩, hz.2⟩
        ⟨w, hw, heq⟩).elim
  · rintro ⟨⟨w, s⟩, ⟨hw, hs⟩, rfl⟩
    have hdiv : 0 ≤ s / a ∧ s / a < 1 :=
      ⟨div_nonneg hs.1 ha.le, (div_lt_one ha).mpr hs.2⟩
    rcases hw with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · refine ⟨⟨(s / a - 2, z), ⟨⟨by linarith, by linarith⟩, hz⟩, ?_⟩,
        ⟨(rim false z, s), ⟨hrim false hz, hs⟩, rfl⟩⟩
      simp only [commonCollarAttachment, if_pos (show s / a - 2 ≤ -1 by linarith)]
      congr 1
      exact Prod.ext rfl (by field_simp; ring)
    · refine ⟨⟨(2 - s / a, z), ⟨⟨by linarith, by linarith⟩, hz⟩, ?_⟩,
        ⟨(rim true z, s), ⟨hrim true hz, hs⟩, rfl⟩⟩
      simp only [commonCollarAttachment, if_neg (show ¬2 - s / a ≤ -1 by linarith),
        if_pos (show 1 ≤ 2 - s / a by linarith)]
      congr 1
      exact Prod.ext rfl (by field_simp; ring)

end PoincareConjecture.M76
