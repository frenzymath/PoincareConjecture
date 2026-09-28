import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Set.Card

set_option autoImplicit false

namespace Submodule

theorem le_of_mem_of_support_minimal
    {k E : Type*} [Field k] [Finite E] (K L : Submodule k (E → k))
    (hminimal : ∀ x ∈ K, x ≠ 0 →
      (∀ y ∈ K, y ≠ 0 → Function.support y ⊆ Function.support x →
        Function.support x ⊆ Function.support y) → x ∈ L) :
    K ≤ L := by
  classical
  suffices h : ∀ n : ℕ, ∀ x ∈ K, (Function.support x).ncard = n → x ∈ L by
    exact fun x hx => h _ x hx rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hx hn
    by_cases hxzero : x = 0
    · simpa only [hxzero] using L.zero_mem
    by_cases hmin : ∀ y ∈ K, y ≠ 0 → Function.support y ⊆ Function.support x →
        Function.support x ⊆ Function.support y
    · exact hminimal x hx hxzero hmin
    push Not at hmin
    obtain ⟨y, hy, hyzero, hyx, hnxy⟩ := hmin
    have hysmall : (Function.support y).ncard < n := by
      rw [← hn]
      exact Set.ncard_lt_ncard ⟨hyx, hnxy⟩
    have hyL : y ∈ L := ih _ hysmall y hy rfl
    obtain ⟨e, he⟩ : ∃ e, y e ≠ 0 := by
      by_contra h
      apply hyzero
      funext e
      push Not at h
      exact h e
    let c := x e / y e
    let z := x - c • y
    have hzK : z ∈ K := K.sub_mem hx (K.smul_mem c hy)
    have hzx : Function.support z ⊆ Function.support x := by
      intro i hzi
      by_contra hxi
      have hxi' : x i = 0 := not_not.mp hxi
      have hyi : y i = 0 := by
        by_contra hyi
        exact hxi (hyx hyi)
      exact hzi (by simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hxi', hyi, mul_zero, sub_self])
    have hze : z e = 0 := by
      simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c,
        div_mul_cancel₀ _ he, sub_self]
    have hzsmall : (Function.support z).ncard < n := by
      rw [← hn]
      refine Set.ncard_lt_ncard ⟨hzx, ?_⟩ (Set.toFinite _)
      intro hxz
      exact hxz (hyx he) hze
    have hzL : z ∈ L := ih _ hzsmall z hzK rfl
    have hsum : z + c • y = x := sub_add_cancel x (c • y)
    exact hsum ▸ L.add_mem hzL (L.smul_mem c hyL)

end Submodule
