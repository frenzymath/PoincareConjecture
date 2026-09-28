import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false

namespace PoincareConjecture.Proofs.M09

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem triangular_bijective_iff (L : E × ℝ →L[ℝ] F × ℝ) (K : E →L[ℝ] F)
    (htime : ∀ z, (L z).2 = z.2) (hspace : ∀ W, (L (W, 0)).1 = K W) :
    Function.Bijective L ↔ Function.Bijective K := by
  have hsplit (z : E × ℝ) : (L z).1 = K z.1 + (L (0, z.2)).1 := by
    have hz : z = (z.1, 0) + (0, z.2) := by ext <;> simp
    calc
      _ = (L ((z.1, 0) + (0, z.2))).1 := congrArg (fun w ↦ (L w).1) hz
      _ = (L (z.1, 0)).1 + (L (0, z.2)).1 := by rw [map_add]; rfl
      _ = _ := by rw [hspace]
  constructor
  · intro hL
    constructor
    · intro v w hvw
      have he : L (v, 0) = L (w, 0) :=
        Prod.ext (by simpa only [hspace] using hvw) (by simp only [htime])
      exact congrArg Prod.fst (hL.1 he)
    · intro v
      obtain ⟨z, hz⟩ := hL.2 (v, 0)
      have ht : z.2 = 0 := by simpa only [htime] using congrArg Prod.snd hz
      refine ⟨z.1, ?_⟩
      have he := congrArg Prod.fst hz
      rw [hsplit, ht] at he
      have hzero : (L (0, 0)).1 = 0 := by
        change (L (0 : E × ℝ)).1 = 0
        rw [map_zero]
        rfl
      simpa only [hzero, add_zero] using he
  · intro hK
    constructor
    · intro v w hvw
      have ht : v.2 = w.2 := by simpa only [htime] using congrArg Prod.snd hvw
      refine Prod.ext (hK.1 ?_) ht
      have he := congrArg Prod.fst hvw
      rw [hsplit v, hsplit w, ht] at he
      exact add_right_cancel he
    · intro z
      obtain ⟨W, hW⟩ := hK.2 (z.1 - (L (0, z.2)).1)
      refine ⟨(W, z.2), Prod.ext ?_ (htime _)⟩
      rw [hsplit, hW]
      exact sub_add_cancel _ _

end PoincareConjecture.Proofs.M09
