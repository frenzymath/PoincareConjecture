import PoincareConjecture.Proofs.M76.Mathlib.SquareShellSequenceCover

set_option autoImplicit false

open Set

namespace SquareShell

theorem radiusMap_eq_left_iff {a b c d r : ℝ} (hab : a < b) (hcd : c < d) :
    radiusMap a b c d r = c ↔ r = a := by
  constructor
  · intro h
    apply (strictMono_radiusMap hab hcd).injective
    exact h.trans (radiusMap_endpoints hab).1.symm
  · rintro rfl
    exact (radiusMap_endpoints hab).1

theorem radiusMap_eq_right_iff {a b c d r : ℝ} (hab : a < b) (hcd : c < d) :
    radiusMap a b c d r = d ↔ r = b := by
  constructor
  · intro h
    apply (strictMono_radiusMap hab hcd).injective
    exact h.trans (radiusMap_endpoints hab).2.symm
  · rintro rfl
    exact (radiusMap_endpoints hab).2

theorem sequence_shell_overlap_iff {a b : ℕ → ℝ}
    (ha : StrictAnti a) (hb : StrictAnti b)
    (e : ∀ n, shell (a (n + 1)) (a n) ≃ₜ shell (b (n + 1)) (b n))
    (he : ∀ n (x : shell (a (n + 1)) (a n)),
      ‖(e n x : ℝ × ℝ)‖ = radiusMap (a (n + 1)) (a n) (b (n + 1)) (b n) ‖(x : ℝ × ℝ)‖)
    (n m : ℕ) (x : shell (a (n + 1)) (a n)) :
    (x : ℝ × ℝ) ∈ shell (a (m + 1)) (a m) ↔
      (e n x : ℝ × ℝ) ∈ shell (b (m + 1)) (b m) := by
  have houter : ‖(x : ℝ × ℝ)‖ = a n ↔ ‖(e n x : ℝ × ℝ)‖ = b n := by
    rw [he]
    exact (radiusMap_eq_right_iff (ha (Nat.lt_succ_self n))
      (hb (Nat.lt_succ_self n))).symm
  have hinner : ‖(x : ℝ × ℝ)‖ = a (n + 1) ↔ ‖(e n x : ℝ × ℝ)‖ = b (n + 1) := by
    rw [he]
    exact (radiusMap_eq_left_iff (ha (Nat.lt_succ_self n))
      (hb (Nat.lt_succ_self n))).symm
  change ‖(x : ℝ × ℝ)‖ ∈ Icc (a (m + 1)) (a m) ↔
    ‖(e n x : ℝ × ℝ)‖ ∈ Icc (b (m + 1)) (b m)
  rw [ha.mem_adjacent_Icc_iff x.property, hb.mem_adjacent_Icc_iff (e n x).property,
    houter, hinner]

theorem sequence_shell_agree {a b : ℕ → ℝ} (ha : StrictAnti a)
    (e : ∀ n, shell (a (n + 1)) (a n) ≃ₜ shell (b (n + 1)) (b n))
    (hinner : ∀ n (x : shell (a (n + 1)) (a n)), ‖(x : ℝ × ℝ)‖ = a (n + 1) →
      (e n x : ℝ × ℝ) = (b (n + 1) / a (n + 1)) • (x : ℝ × ℝ))
    (houter : ∀ n (x : shell (a (n + 1)) (a n)), ‖(x : ℝ × ℝ)‖ = a n →
      (e n x : ℝ × ℝ) = (b n / a n) • (x : ℝ × ℝ))
    (n m : ℕ) (x : ℝ × ℝ) (hn : x ∈ shell (a (n + 1)) (a n))
    (hm : x ∈ shell (a (m + 1)) (a m)) :
    (e n ⟨x, hn⟩ : ℝ × ℝ) = e m ⟨x, hm⟩ := by
  rcases (ha.mem_adjacent_Icc_iff hn).mp hm with heq | ⟨hi, hr⟩ | ⟨hi, hr⟩
  · subst m
    rfl
  · have hr' : ‖x‖ = a (m + 1) := hr.trans (congrArg a hi).symm
    rw [houter n ⟨x, hn⟩ hr, hinner m ⟨x, hm⟩ hr']
    change (b n / a n) • x = (b (m + 1) / a (m + 1)) • x
    rw [hi]
  · have hr' : ‖x‖ = a m := hr.trans (congrArg a hi)
    rw [hinner n ⟨x, hn⟩ hr, houter m ⟨x, hm⟩ hr']
    change (b (n + 1) / a (n + 1)) • x = (b m / a m) • x
    rw [hi]

theorem sequence_shell_open_membership {a b : ℕ → ℝ} {c d : ℝ}
    (ha : StrictAnti a) (hb : StrictAnti b) (hc : ∀ n, c < a n) (hd : ∀ n, d < b n)
    (e : ∀ n, shell (a (n + 1)) (a n) ≃ₜ shell (b (n + 1)) (b n))
    (he : ∀ n (x : shell (a (n + 1)) (a n)),
      ‖(e n x : ℝ × ℝ)‖ = radiusMap (a (n + 1)) (a n) (b (n + 1)) (b n) ‖(x : ℝ × ℝ)‖)
    (n : ℕ) (x : shell (a (n + 1)) (a n)) :
    ‖(x : ℝ × ℝ)‖ ∈ Ioo c (a 0) ↔ ‖(e n x : ℝ × ℝ)‖ ∈ Ioo d (b 0) := by
  have hclow : c < ‖(x : ℝ × ℝ)‖ := (hc (n + 1)).trans_le x.property.1
  have hdlow : d < ‖(e n x : ℝ × ℝ)‖ := (hd (n + 1)).trans_le (e n x).property.1
  by_cases hn : n = 0
  · subst n
    have hmono := strictMono_radiusMap (ha (Nat.lt_succ_self 0)) (hb (Nat.lt_succ_self 0))
    have hend := (radiusMap_endpoints (c := b 1) (d := b 0) (ha (Nat.lt_succ_self 0))).2
    constructor
    · intro hx
      refine ⟨hdlow, ?_⟩
      calc
        ‖(e 0 x : ℝ × ℝ)‖ =
            radiusMap (a 1) (a 0) (b 1) (b 0) ‖(x : ℝ × ℝ)‖ := he 0 x
        _ < radiusMap (a 1) (a 0) (b 1) (b 0) (a 0) := hmono hx.2
        _ = b 0 := hend
    · intro hx
      refine ⟨hclow, ?_⟩
      apply hmono.lt_iff_lt.mp
      calc
        radiusMap (a 1) (a 0) (b 1) (b 0) ‖(x : ℝ × ℝ)‖ =
            ‖(e 0 x : ℝ × ℝ)‖ := (he 0 x).symm
        _ < b 0 := hx.2
        _ = radiusMap (a 1) (a 0) (b 1) (b 0) (a 0) := hend.symm
  · exact iff_of_true
      ⟨hclow, x.property.2.trans_lt (ha (Nat.pos_of_ne_zero hn))⟩
      ⟨hdlow, (e n x).property.2.trans_lt (hb (Nat.pos_of_ne_zero hn))⟩

end SquareShell
