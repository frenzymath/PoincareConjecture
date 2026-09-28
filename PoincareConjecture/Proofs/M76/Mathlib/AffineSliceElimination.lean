import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace AffineMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem image_zeroLevel_of_nonnegative_displacement (A : E →ᵃ[ℝ] ℝ)
    {S d : Set E} (hdS : d ⊆ S) (hdplane : d ⊆ {x | A x = 0})
    (q v : E) (hv : A.linear v = 1) (g : E → ℝ)
    (hg : ∀ x ∈ S, 0 ≤ g x) (hdzero : ∀ x ∈ d, g x = 0 ↔ x = q)
    (hneg : ∀ x ∈ S, A x < 0 → g x = 0)
    (hother : ∀ x ∈ S, A x = 0 → x ∉ d → g x = 0)
    {t : ℝ} (ht : 0 < t) (H : E → E)
    (hH : ∀ x ∈ S, H x = x + (t * g x) • v) :
    H '' S ∩ {x | A x = 0} = ((S ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q}) := by
  have hheight (x : E) (hx : x ∈ S) : A (H x) = A x + t * g x := by
    rw [hH x hx, add_comm x]
    change A ((t * g x) • v +ᵥ x) = A x + t * g x
    rw [A.map_vadd, map_smul, hv]
    simp [add_comm]
  have hfix (x : E) (hx : x ∈ S) (hz : g x = 0) : H x = x := by
    rw [hH x hx, hz, mul_zero, zero_smul, add_zero]
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hzero⟩
    have heq : A y + t * g y = 0 := (hheight y hy).symm.trans hzero
    have hyA : A y = 0 := by
      rcases lt_trichotomy (A y) 0 with hlt | he | hgt
      · rw [hneg y hy hlt, mul_zero, add_zero] at heq
        exact heq
      · exact he
      · have hn := mul_nonneg ht.le (hg y hy)
        linarith
    have hgy : g y = 0 := by
      rw [hyA, zero_add] at heq
      exact (mul_eq_zero.mp heq).resolve_left ht.ne'
    rw [hfix y hy hgy]
    by_cases hyd : y ∈ d
    · exact Or.inr ⟨hyd, (hdzero y hyd).mp hgy⟩
    · exact Or.inl ⟨⟨hy, hyA⟩, hyd⟩
  · rintro (⟨⟨hxS, hxA⟩, hxd⟩ | ⟨hxd, hxq⟩)
    · exact ⟨⟨x, hxS, hfix x hxS (hother x hxS hxA hxd)⟩, hxA⟩
    · exact ⟨⟨x, hdS hxd, hfix x (hdS hxd) ((hdzero x hxd).mpr hxq)⟩, hdplane hxd⟩

end AffineMap
