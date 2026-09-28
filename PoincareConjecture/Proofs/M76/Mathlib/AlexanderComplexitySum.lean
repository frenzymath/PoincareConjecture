import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Notation.Support
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset











set_option autoImplicit false

open Set

namespace Nat

variable {L : Type*} [Fintype L]





theorem sum_pair_decrease_of_strict_at_one
    (n n₀ n₁ : L → ℕ) (j : L)
    (h : ∀ i, n₀ i + n₁ i ≤ n i) (hj : n₀ j + n₁ j < n j) :
    (∑ i, n₀ i) + (∑ i, n₁ i) < ∑ i, n i ∧
      (∑ i, n₀ i) < ∑ i, n i ∧ (∑ i, n₁ i) < ∑ i, n i := by
  have hsum : (∑ i, (n₀ i + n₁ i)) < ∑ i, n i :=
    Finset.sum_lt_sum (fun i _ => h i) ⟨j, Finset.mem_univ j, hj⟩
  rw [Finset.sum_add_distrib] at hsum
  exact ⟨hsum, by omega, by omega⟩





theorem sum_pair_decrease_of_one_deleted
    (n n₀ n₁ : L → ℕ) (j : L)
    (hj : n₀ j + n₁ j + 1 = n j)
    (hother : ∀ i, i ≠ j → n₀ i + n₁ i = n i) :
    (∑ i, n₀ i) + (∑ i, n₁ i) + 1 = ∑ i, n i ∧
      (∑ i, n₀ i) < ∑ i, n i ∧ (∑ i, n₁ i) < ∑ i, n i := by
  classical
  have hlocal (i : L) : n₀ i + n₁ i + (if i = j then 1 else 0) = n i := by
    by_cases hi : i = j
    · subst i
      simpa using hj
    · simpa only [if_neg hi, add_zero] using hother i hi
  have hsum : (∑ i, n₀ i) + (∑ i, n₁ i) + 1 = ∑ i, n i := by
    calc
      (∑ i, n₀ i) + (∑ i, n₁ i) + 1 =
          ∑ i, (n₀ i + n₁ i + (if i = j then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
          if_true]
      _ = ∑ i, n i := Finset.sum_congr rfl (fun i _ => hlocal i)
  exact ⟨hsum, by omega, by omega⟩






theorem card_curve_partition_after_one_deletion
    (C : L → Type*) [∀ l, Finite (C l)] (p : Sigma C)
    (I : Set {x : Sigma C // x ≠ p}) :
    Nat.card I + Nat.card (Iᶜ : Set {x : Sigma C // x ≠ p}) + 1 =
        ∑ l, Nat.card (C l) ∧
      Nat.card I < ∑ l, Nat.card (C l) ∧
      Nat.card (Iᶜ : Set {x : Sigma C // x ≠ p}) < ∑ l, Nat.card (C l) := by
  classical
  let _ (l : L) : Fintype (C l) := Fintype.ofFinite (C l)
  have hpartition : Nat.card I + Nat.card (Iᶜ : Set {x : Sigma C // x ≠ p}) =
      Nat.card {x : Sigma C // x ≠ p} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.Set.sumCompl I)
  have hdelete : Nat.card {x : Sigma C // x ≠ p} = Nat.card (Sigma C) - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simpa only [Fintype.card_subtype_eq] using
      (Fintype.card_subtype_compl (fun x : Sigma C => x = p))
  have hpos : 0 < Nat.card (Sigma C) := Nat.card_pos_iff.mpr ⟨⟨p⟩, inferInstance⟩
  rw [Nat.card_sigma] at hdelete hpos
  exact ⟨by omega, by omega, by omega⟩





theorem finite_support_pair_decrease {X : Type*}
    (n n₀ n₁ : X → ℕ) (hn : (Function.support n).Finite)
    (h : ∀ x, n₀ x + n₁ x ≤ n x) (j : X) (hj : n₀ j + n₁ j < n j) :
    ∃ h₀ : (Function.support n₀).Finite, ∃ h₁ : (Function.support n₁).Finite,
      (∑ x ∈ h₀.toFinset, n₀ x) + (∑ x ∈ h₁.toFinset, n₁ x) <
          ∑ x ∈ hn.toFinset, n x ∧
        (∑ x ∈ h₀.toFinset, n₀ x) < ∑ x ∈ hn.toFinset, n x ∧
        (∑ x ∈ h₁.toFinset, n₁ x) < ∑ x ∈ hn.toFinset, n x := by
  classical
  have hs₀ : Function.support n₀ ⊆ Function.support n := by
    intro x hx
    change n₀ x ≠ 0 at hx
    change n x ≠ 0
    intro hz
    have hbound := h x
    exact hx (by omega)
  have hs₁ : Function.support n₁ ⊆ Function.support n := by
    intro x hx
    change n₁ x ≠ 0 at hx
    change n x ≠ 0
    intro hz
    have hbound := h x
    exact hx (by omega)
  have h₀ := hn.subset hs₀
  have h₁ := hn.subset hs₁
  have hsum₀ : (∑ x ∈ h₀.toFinset, n₀ x) = ∑ x ∈ hn.toFinset, n₀ x := by
    apply Finset.sum_subset
    · intro x hx
      exact hn.mem_toFinset.mpr (hs₀ (h₀.mem_toFinset.mp hx))
    · intro x _ hx
      by_contra hne
      exact hx (h₀.mem_toFinset.mpr hne)
  have hsum₁ : (∑ x ∈ h₁.toFinset, n₁ x) = ∑ x ∈ hn.toFinset, n₁ x := by
    apply Finset.sum_subset
    · intro x hx
      exact hn.mem_toFinset.mpr (hs₁ (h₁.mem_toFinset.mp hx))
    · intro x _ hx
      by_contra hne
      exact hx (h₁.mem_toFinset.mpr hne)
  have hjmem : j ∈ hn.toFinset := by
    apply hn.mem_toFinset.mpr
    change n j ≠ 0
    omega
  have hsum : (∑ x ∈ hn.toFinset, (n₀ x + n₁ x)) < ∑ x ∈ hn.toFinset, n x :=
    Finset.sum_lt_sum (fun x _ => h x) ⟨j, hjmem, hj⟩
  rw [Finset.sum_add_distrib, ← hsum₀, ← hsum₁] at hsum
  exact ⟨h₀, h₁, hsum, by omega, by omega⟩

end Nat
