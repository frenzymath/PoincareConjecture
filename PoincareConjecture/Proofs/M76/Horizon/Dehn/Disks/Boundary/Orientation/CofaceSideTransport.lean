import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.NumberedTriangleParity

set_option autoImplicit false

open AbstractSimplicialComplex PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.Dehn

def orderedCofaceParity {V : Type*} [DecidableEq V]
    (number : V → ℕ) (t : Finset V) (a b : V) : ZMod 2 :=
  boundaryFaceParity number t {a, b} + if number b < number a then 1 else 0

theorem orderedCofaceParity_reverse_of_label_ne {V : Type*} [DecidableEq V]
    (number : V → ℕ) (t : Finset V) {a b : V} (hn : number a ≠ number b) :
    orderedCofaceParity number t a b + orderedCofaceParity number t b a = 1 := by
  rcases lt_or_gt_of_ne hn with h | h
  · simp only [orderedCofaceParity, Finset.pair_comm b a,
      if_pos h, if_neg (not_lt_of_gt h)]
    rw [add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · simp only [orderedCofaceParity, Finset.pair_comm b a,
      if_pos h, if_neg (not_lt_of_gt h)]
    rw [add_zero, add_right_comm, CharTwo.add_self_eq_zero, zero_add]

theorem orderedCofaceParity_reverse {V : Type*} [DecidableEq V]
    (number : V ↪ ℕ) (t : Finset V) {a b : V} (hab : a ≠ b) :
    orderedCofaceParity number t a b + orderedCofaceParity number t b a = 1 :=
  orderedCofaceParity_reverse_of_label_ne number t (fun h ↦ hab (number.injective h))

theorem orderedCofaceParity_triangle_of_label_ne {V : Type*} [DecidableEq V]
    (number : V → ℕ) {v a b : V} (hnva : number v ≠ number a)
    (hnvb : number v ≠ number b) (hnab : number a ≠ number b) :
    orderedCofaceParity number {v, a, b} v a +
      orderedCofaceParity number {v, a, b} v b = 1 := by
  have hva : v ≠ a := fun h ↦ hnva (congrArg number h)
  have hvb : v ≠ b := fun h ↦ hnvb (congrArg number h)
  have hab : a ≠ b := fun h ↦ hnab (congrArg number h)
  have hda : ({v, a, b} : Finset V) \ {v, a} = {b} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  have hdb : ({v, a, b} : Finset V) \ {v, b} = {a} := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    grind
  simp only [orderedCofaceParity, boundaryFaceParity, hda, hdb, Finset.sum_singleton]
  rcases lt_or_gt_of_ne hnva with h₀ | h₀ <;>
    rcases lt_or_gt_of_ne hnvb with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hnab with h₂ | h₂
  all_goals first | omega | skip
  all_goals
    norm_num [hva, hvb, hab, h₀, h₁, h₂, not_lt_of_gt h₀, not_lt_of_gt h₁,
      not_lt_of_gt h₂, Finset.filter_insert, Finset.filter_singleton]
    decide

theorem orderedCofaceParity_triangle {V : Type*} [DecidableEq V]
    (number : V ↪ ℕ) {v a b : V} (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b) :
    orderedCofaceParity number {v, a, b} v a +
      orderedCofaceParity number {v, a, b} v b = 1 :=
  orderedCofaceParity_triangle_of_label_ne number
    (fun h ↦ hva (number.injective h)) (fun h ↦ hvb (number.injective h))
    (fun h ↦ hab (number.injective h))

theorem orderedCofaceParity_cancellation {V : Type*} [DecidableEq V]
    (number : V → ℕ) (t u : Finset V) (a b : V) (st su : ZMod 2)
    (h : (st + boundaryFaceParity number t {a, b}) +
      (su + boundaryFaceParity number u {a, b}) = 1) :
    (st + orderedCofaceParity number t a b) +
      (su + orderedCofaceParity number u a b) = 1 := by
  unfold orderedCofaceParity
  calc
    _ = ((st + boundaryFaceParity number t {a, b}) +
        (su + boundaryFaceParity number u {a, b})) +
        ((if number b < number a then 1 else 0 : ZMod 2) +
          (if number b < number a then 1 else 0 : ZMod 2)) := by ring
    _ = 1 := by rw [h, CharTwo.add_self_eq_zero, add_zero]

theorem orderedCofaceParity_chain_of_label_ne {V : Type*} [DecidableEq V]
    (number : V → ℕ) (v : V) (p : ℕ → V) (t : ℕ → Finset V)
    (sigma : ℕ → ZMod 2) (n : ℕ)
    (htriangle : ∀ k ≤ n, t k = {v, p k, p (k + 1)})
    (hvertices : ∀ k ≤ n, number v ≠ number (p k) ∧
      number v ≠ number (p (k + 1)) ∧ number (p k) ≠ number (p (k + 1)))
    (hcancel : ∀ k < n,
      (sigma k + boundaryFaceParity number (t k) {v, p (k + 1)}) +
        (sigma (k + 1) + boundaryFaceParity number (t (k + 1)) {v, p (k + 1)}) = 1) :
    (sigma 0 + orderedCofaceParity number (t 0) v (p 0)) +
      (sigma n + orderedCofaceParity number (t n) v (p (n + 1))) = 1 := by
  induction n with
  | zero =>
      have hp := hvertices 0 (Nat.le_refl 0)
      have h := orderedCofaceParity_triangle_of_label_ne number hp.1 hp.2.1 hp.2.2
      rw [← htriangle 0 (Nat.le_refl 0)] at h
      calc
        _ = (sigma 0 + sigma 0) +
            (orderedCofaceParity number (t 0) v (p 0) +
              orderedCofaceParity number (t 0) v (p 1)) := by ring
        _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add, h]
  | succ n ih =>
      have hprev := ih (fun k hk ↦ htriangle k (hk.trans (Nat.le_succ n)))
        (fun k hk ↦ hvertices k (hk.trans (Nat.le_succ n)))
        (fun k hk ↦ hcancel k (hk.trans_le (Nat.le_succ n)))
      have hcross := orderedCofaceParity_cancellation number (t n) (t (n + 1))
        v (p (n + 1)) (sigma n) (sigma (n + 1)) (hcancel n (Nat.lt_succ_self n))
      have hp := hvertices (n + 1) (Nat.le_refl _)
      have hlast := orderedCofaceParity_triangle_of_label_ne number hp.1 hp.2.1 hp.2.2
      rw [← htriangle (n + 1) (Nat.le_refl _)] at hlast
      have hlast' :
          (sigma (n + 1) + orderedCofaceParity number (t (n + 1)) v (p (n + 1))) +
            (sigma (n + 1) + orderedCofaceParity number (t (n + 1)) v (p (n + 1 + 1))) =
            1 := by
        calc
          _ = (sigma (n + 1) + sigma (n + 1)) +
              (orderedCofaceParity number (t (n + 1)) v (p (n + 1)) +
                orderedCofaceParity number (t (n + 1)) v (p (n + 1 + 1))) := by ring
          _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add, hlast]
      linear_combination hprev - hcross + hlast'

theorem orderedCofaceParity_chain {V : Type*} [DecidableEq V]
    (number : V ↪ ℕ) (v : V) (p : ℕ → V) (t : ℕ → Finset V)
    (sigma : ℕ → ZMod 2) (n : ℕ)
    (htriangle : ∀ k ≤ n, t k = {v, p k, p (k + 1)})
    (hvertices : ∀ k ≤ n, v ≠ p k ∧ v ≠ p (k + 1) ∧ p k ≠ p (k + 1))
    (hcancel : ∀ k < n,
      (sigma k + boundaryFaceParity number (t k) {v, p (k + 1)}) +
        (sigma (k + 1) + boundaryFaceParity number (t (k + 1)) {v, p (k + 1)}) = 1) :
    (sigma 0 + orderedCofaceParity number (t 0) v (p 0)) +
      (sigma n + orderedCofaceParity number (t n) v (p (n + 1))) = 1 :=
  orderedCofaceParity_chain_of_label_ne number v p t sigma n htriangle
    (fun k hk ↦ ⟨fun h ↦ (hvertices k hk).1 (number.injective h),
      fun h ↦ (hvertices k hk).2.1 (number.injective h),
      fun h ↦ (hvertices k hk).2.2 (number.injective h)⟩) hcancel

theorem orderedCofaceParity_through_vertex_of_label_ne {V : Type*} [DecidableEq V]
    (number : V → ℕ) (v : V) (p : ℕ → V) (t : ℕ → Finset V)
    (sigma : ℕ → ZMod 2) (n : ℕ)
    (htriangle : ∀ k ≤ n, t k = {v, p k, p (k + 1)})
    (hvertices : ∀ k ≤ n, number v ≠ number (p k) ∧
      number v ≠ number (p (k + 1)) ∧ number (p k) ≠ number (p (k + 1)))
    (hcancel : ∀ k < n,
      (sigma k + boundaryFaceParity number (t k) {v, p (k + 1)}) +
        (sigma (k + 1) + boundaryFaceParity number (t (k + 1)) {v, p (k + 1)}) = 1) :
    sigma 0 + orderedCofaceParity number (t 0) (p 0) v =
      sigma n + orderedCofaceParity number (t n) v (p (n + 1)) := by
  have hchain := orderedCofaceParity_chain_of_label_ne number v p t sigma n
    htriangle hvertices hcancel
  have hreverse := orderedCofaceParity_reverse_of_label_ne number (t 0)
    (hvertices 0 (Nat.zero_le n)).1
  have hdouble : sigma 0 + sigma 0 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hreverse - hchain + hdouble

theorem orderedCofaceParity_through_vertex {V : Type*} [DecidableEq V]
    (number : V ↪ ℕ) (v : V) (p : ℕ → V) (t : ℕ → Finset V)
    (sigma : ℕ → ZMod 2) (n : ℕ)
    (htriangle : ∀ k ≤ n, t k = {v, p k, p (k + 1)})
    (hvertices : ∀ k ≤ n, v ≠ p k ∧ v ≠ p (k + 1) ∧ p k ≠ p (k + 1))
    (hcancel : ∀ k < n,
      (sigma k + boundaryFaceParity number (t k) {v, p (k + 1)}) +
        (sigma (k + 1) + boundaryFaceParity number (t (k + 1)) {v, p (k + 1)}) = 1) :
    sigma 0 + orderedCofaceParity number (t 0) (p 0) v =
      sigma n + orderedCofaceParity number (t n) v (p (n + 1)) := by
  have hchain := orderedCofaceParity_chain number v p t sigma n htriangle hvertices hcancel
  have hreverse := orderedCofaceParity_reverse number (t 0)
    (hvertices 0 (Nat.zero_le n)).1
  have hdouble : sigma 0 + sigma 0 = 0 := CharTwo.add_self_eq_zero _
  linear_combination hreverse - hchain + hdouble

end PoincareConjecture.M76.Dehn
