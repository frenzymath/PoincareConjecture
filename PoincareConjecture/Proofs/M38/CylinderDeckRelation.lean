import PoincareConjecture.Definitions.Ch09.NeckCapTopology

set_option autoImplicit false

namespace PoincareConjecture.M38

def CylinderDeckRelated (period : ℝ) (x y : RoundCylinderSpace) : Prop :=
  ∃ n : ℤ, (x.1 = y.1 ∧ x.2 = y.2 + (n : ℝ) * period) ∨
    (x.1 = -y.1 ∧ x.2 = (n : ℝ) * period - y.2)

namespace CylinderDeckRelated

theorem refl (period : ℝ) (x : RoundCylinderSpace) : CylinderDeckRelated period x x :=
  ⟨0, Or.inl ⟨rfl, by simp⟩⟩

theorem symm {period : ℝ} {x y : RoundCylinderSpace}
    (h : CylinderDeckRelated period x y) : CylinderDeckRelated period y x := by
  rcases h with ⟨n, h | h⟩
  · refine ⟨-n, Or.inl ⟨h.1.symm, ?_⟩⟩
    rw [h.2, Int.cast_neg]
    ring
  · refine ⟨n, Or.inr ⟨?_, ?_⟩⟩
    · rw [h.1, neg_neg]
    · rw [h.2]
      ring

theorem trans {period : ℝ} {x y z : RoundCylinderSpace}
    (h : CylinderDeckRelated period x y) (k : CylinderDeckRelated period y z) :
    CylinderDeckRelated period x z := by
  rcases h with ⟨n, h | h⟩ <;> rcases k with ⟨m, k | k⟩
  · refine ⟨n + m, Or.inl ⟨h.1.trans k.1, ?_⟩⟩
    rw [h.2, k.2, Int.cast_add]
    ring
  · refine ⟨n + m, Or.inr ⟨h.1.trans k.1, ?_⟩⟩
    rw [h.2, k.2, Int.cast_add]
    ring
  · refine ⟨n - m, Or.inr ⟨h.1.trans (congrArg Neg.neg k.1), ?_⟩⟩
    rw [h.2, k.2, Int.cast_sub]
    ring
  · refine ⟨n - m, Or.inl ⟨?_, ?_⟩⟩
    · rw [h.1, k.1, neg_neg]
    · rw [h.2, k.2, Int.cast_sub]
      ring

end CylinderDeckRelated

end PoincareConjecture.M38
