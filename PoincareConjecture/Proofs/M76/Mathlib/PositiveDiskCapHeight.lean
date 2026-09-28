import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskLevels

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_positive_cap_height {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc (2 / 3) 1 ∧ (r x = 1 ↔ x ∈ b)) ∧
      (∃ p ∈ d \ b, r p = 2 / 3 ∧ ∀ x ∈ d, r x = 2 / 3 ↔ x = p) ∧
      ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
        IsFinitePLBallPair (ℝ × ℝ) (d ∩ {x | r x ≤ a}) (d ∩ {x | r x = a}) := by
  obtain ⟨f, hf, hfzero, ⟨p, hp, hfp, hfmax⟩, hlevels⟩ := hd.exists_roof_with_disk_levels
  let r : E → ℝ := fun x => 1 - f x
  let a : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ
  have hr : FinitePiecewiseAffineOn r d := hf.postcomp a
  have hpmin : r p = 2 / 3 := by dsimp [r]; rw [hfp]; norm_num
  refine ⟨r, hr, ?_, ⟨p, hp, hpmin, ?_⟩, ?_⟩
  · intro x hx
    have hlo := (hfzero x hx).1
    have hhi := (hfmax x hx).1
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change 2 / 3 ≤ 1 - f x
      linarith
    · change 1 - f x ≤ 1
      linarith
    · have heq : r x = 1 ↔ f x = 0 := by
        dsimp [r]
        constructor <;> intro h <;> linarith
      exact heq.trans (hfzero x hx).2
  · intro x hx
    have heq : r x = 2 / 3 ↔ f x = 1 / 3 := by
      dsimp [r]
      constructor <;> intro h <;> linarith
    exact heq.trans (hfmax x hx).2
  · intro t ht
    have h := hlevels (1 - t) (by linarith [ht.2]) (by linarith [ht.1])
    have hsub : {x : E | 1 - t ≤ f x} = {x | r x ≤ t} := by
      ext x
      change 1 - t ≤ f x ↔ 1 - f x ≤ t
      constructor <;> intro hx <;> linarith
    have heq : {x : E | f x = 1 - t} = {x | r x = t} := by
      ext x
      change f x = 1 - t ↔ 1 - f x = t
      constructor <;> intro hx <;> linarith
    rwa [hsub, heq] at h

end Set
