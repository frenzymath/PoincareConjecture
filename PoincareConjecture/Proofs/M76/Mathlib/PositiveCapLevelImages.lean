import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLevelImages










set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]




theorem FinitePiecewiseAffineOn.positive_cap_level_classification
    {d b : Set E} {f : E → F} (hf : FinitePiecewiseAffineOn f d)
    (hinj : InjOn f d) {r : E → ℝ} {A : F → ℝ} {t : ℝ} (ht : 0 < t)
    (hheight : ∀ x ∈ d, A (f x) = t * r x)
    (hr : ∀ x ∈ d, r x ∈ Icc (2 / 3) 1 ∧ (r x = 1 ↔ x ∈ b))
    {p : E} (hp : p ∈ d) (hpmin : r p = 2 / 3)
    (hunique : ∀ x ∈ d, r x = 2 / 3 ↔ x = p)
    (hlevels : ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
      IsFinitePLBallPair (ℝ × ℝ) (d ∩ {x | r x ≤ a}) (d ∩ {x | r x = a}))
    (hb : b ⊆ d) :
    (∀ c : ℝ, c < t * (2 / 3) ∨ t < c → (f '' d) ∩ {x | A x = c} = ∅) ∧
      (f '' d) ∩ {x | A x = t * (2 / 3)} = {f p} ∧
      (f '' d) ∩ {x | A x = t} = f '' b ∧
      ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
        IsFinitePLBallPair (ℝ × ℝ) ((f '' d) ∩ {x | A x ≤ t * a})
          ((f '' d) ∩ {x | A x = t * a}) := by
  refine ⟨?_, ?_, ?_, fun a ha =>
    hf.image_sublevel_ballPair hinj Subset.rfl ht hheight (hlevels a ha)⟩
  · intro c hc
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨⟨y, hy, rfl⟩, hyc⟩
    have hh : t * r y = c := (hheight y hy).symm.trans hyc
    have hlo := (hr y hy).1.1
    have hhi := (hr y hy).1.2
    rcases hc with hc | hc <;> nlinarith
  · ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hym⟩
      have hrmin : r y = 2 / 3 :=
        mul_left_cancel₀ ht.ne' ((hheight y hy).symm.trans hym)
      rw [(hunique y hy).mp hrmin]
      exact mem_singleton _
    · intro hx
      rw [show x = f p from hx]
      exact ⟨mem_image_of_mem f hp, (hheight p hp).trans (congrArg (t * ·) hpmin)⟩
  · ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyr⟩
      have hrone : r y = 1 := mul_left_cancel₀ ht.ne'
        ((hheight y hy).symm.trans (hyr.trans (mul_one t).symm))
      exact mem_image_of_mem f ((hr y hy).2.mp hrone)
    · rintro ⟨y, hy, rfl⟩
      refine ⟨mem_image_of_mem f (hb hy), ?_⟩
      change A (f y) = t
      rw [hheight y (hb hy), (hr y (hb hy)).2.mpr hy, mul_one]

end Geometry
