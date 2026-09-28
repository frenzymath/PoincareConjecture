import PoincareConjecture.Proofs.M76.Mathlib.AffineCornerStraightening










set_option autoImplicit false

open Set Geometry

namespace ContinuousAffineMap






theorem exists_union_corner_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a b : E →ᴬ[ℝ] ℝ) (v w : E)
    (hav : a.contLinear v = 1) (hbv : b.contLinear v = 0)
    (haw : a.contLinear w = 0) (hbw : b.contLinear w = 1) :
    ∃ H : E ≃ₜ E, H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ y, a (H y) = max (a y) (b y)) ∧
      (∀ y, b (H y) = b y - a y) ∧
      (∀ y, a y = 0 → b y = 0 → H y = y) ∧
      (∀ y, (0 ≤ a y ∨ 0 ≤ b y) ↔ 0 ≤ a (H y)) ∧
      ∀ y, a (H y) = 0 ↔
        (a y = 0 ∧ b y ≤ 0) ∨ (b y = 0 ∧ a y ≤ 0) := by
  have hanv : (-a).contLinear (-v) = 1 := by
    change -a.contLinear (-v) = 1
    rw [map_neg, neg_neg, hav]
  have hbnv : (-b).contLinear (-v) = 0 := by
    change -b.contLinear (-v) = 0
    rw [map_neg, neg_neg, hbv]
  have hanw : (-a).contLinear (-w) = 0 := by
    change -a.contLinear (-w) = 0
    rw [map_neg, neg_neg, haw]
  have hbnw : (-b).contLinear (-w) = 1 := by
    change -b.contLinear (-w) = 1
    rw [map_neg, neg_neg, hbw]
  obtain ⟨H, hHPL, hmin, hdiff, hfix, _, _, _⟩ :=
    (-a).exists_corner_straightening (-b) (-v) (-w) hanv hbnv hanw hbnw
  have hmax (y : E) : a (H y) = max (a y) (b y) := by
    have h := hmin y
    change -a (H y) = min (-a y) (-b y) at h
    rw [min_neg_neg] at h
    exact neg_injective h
  refine ⟨H, hHPL, hmax, ?_, ?_, ?_, ?_⟩
  · intro y
    have h := hdiff y
    change -b (H y) = -b y - -a y at h
    linarith
  · intro y hay hby
    exact hfix y (by simp only [neg_apply, hay, neg_zero])
      (by simp only [neg_apply, hby, neg_zero])
  · intro y
    rw [hmax]
    exact le_max_iff.symm
  · intro y
    rw [hmax, max_eq_iff]
    constructor
    · rintro (⟨ha, hba⟩ | ⟨hb, hab⟩)
      · exact Or.inl ⟨ha, by simpa only [ha] using hba⟩
      · exact Or.inr ⟨hb, by simpa only [hb] using hab⟩
    · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
      · exact Or.inl ⟨ha, by simpa only [ha] using hb⟩
      · exact Or.inr ⟨hb, by simpa only [hb] using ha⟩

end ContinuousAffineMap
