import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D

structure IsNoninterlacingMatching {n : ℕ} (m : Fin n → Fin n) : Prop where

  involutive : Function.Involutive m

  ne_self : ∀ i, m i ≠ i

  noninterlacing : ∀ a b, a < b → b < m a → m a < m b → False

namespace IsNoninterlacingMatching

variable {n : ℕ} {m : Fin n → Fin n} (hm : IsNoninterlacingMatching m)

include hm

private theorem mate_mem_Ioo {a b x : Fin n} (hab : m a = b)
    (hax : a < x) (hxb : x < b) : a < m x ∧ m x < b := by
  have hnea : m x ≠ a := by
    intro h
    have hh := congrArg m h
    rw [hm.involutive, hab] at hh
    exact (ne_of_lt hxb) hh
  have hneb : m x ≠ b := by
    intro h
    have hh := hm.involutive.injective (h.trans hab.symm)
    exact (ne_of_gt hax) hh
  constructor
  · by_contra h
    have hlt : m x < a := lt_of_le_of_ne (not_lt.mp h) hnea
    exact hm.noninterlacing (m x) a hlt
      (by rw [hm.involutive]; exact hax) (by rw [hm.involutive, hab]; exact hxb)
  · by_contra h
    have hlt : b < m x := lt_of_le_of_ne (not_lt.mp h) hneb.symm
    exact hm.noninterlacing a x hax (by rw [hab]; exact hxb)
      (by rw [hab]; exact hlt)

private theorem mate_gt_right {z j x : Fin n} (hz : z.val = 0)
    (hj : m z = j) (hjx : j < x) : j < m x := by
  have hzle (y : Fin n) : z ≤ y := by change z.val ≤ y.val; omega
  have hnez : m x ≠ z := by
    intro h
    have hh := congrArg m h
    rw [hm.involutive, hj] at hh
    exact (ne_of_gt hjx) hh
  have hnej : m x ≠ j := by
    intro h
    have hh := hm.involutive.injective (h.trans hj.symm)
    have := hzle j
    subst x
    omega
  have hpos : z < m x := lt_of_le_of_ne (hzle _) hnez.symm
  by_contra h
  have hlt : m x < j := lt_of_le_of_ne (not_lt.mp h) hnej
  have hh := hm.mate_mem_Ioo hj hpos hlt
  rw [hm.involutive] at hh
  exact (not_lt_of_gt hjx) hh.2

private theorem exists_adjacent_interval (l u : Fin n) (hlu : l ≤ u)
    (hclosed : ∀ x, l ≤ x → x ≤ u → l ≤ m x ∧ m x ≤ u) :
    ∃ a b : Fin n, l ≤ a ∧ b ≤ u ∧ a.val + 1 = b.val ∧ m a = b := by
  classical
  let P (d : ℕ) := ∃ a b : Fin n,
    l ≤ a ∧ a < b ∧ b ≤ u ∧ m a = b ∧ b.val - a.val = d
  have hlm : l < m l :=
    lt_of_le_of_ne (hclosed l le_rfl hlu).1 (hm.ne_self l).symm
  have hex : ∃ d, P d :=
    ⟨(m l).val - l.val, l, m l, le_rfl, hlm, (hclosed l le_rfl hlu).2, rfl, rfl⟩
  obtain ⟨a, b, hla, hab, hbu, hpair, hgap⟩ := Nat.find_spec hex
  have hadd : a.val + 1 = b.val := by
    by_contra h
    have hclt : a.val + 1 < b.val := by omega
    let c : Fin n := ⟨a.val + 1, hclt.trans b.isLt⟩
    have hac : a < c := by change a.val < a.val + 1; omega
    have hcb : c < b := hclt
    obtain ⟨hamc, hmcb⟩ := hm.mate_mem_Ioo hpair hac hcb
    have hcmc : c < m c :=
      lt_of_le_of_ne (show c ≤ m c by change a.val + 1 ≤ (m c).val; omega)
        (hm.ne_self c).symm
    have hsmaller : (m c).val - c.val < Nat.find hex := by
      have hc : c.val = a.val + 1 := rfl
      omega
    exact Nat.find_min hex hsmaller
      ⟨c, m c, hla.trans hac.le, hcmc, hmcb.le.trans hbu, rfl, rfl⟩
  exact ⟨a, b, hla, hbu, hadd, hpair⟩

private theorem exists_adjacent_before {z j : Fin n} (hz : z.val = 0)
    (hpair : m z = j) (hj : 1 < j.val) :
    ∃ a b : Fin n, 0 < a.val ∧ b < j ∧ a.val + 1 = b.val ∧ m a = b := by
  let l : Fin n := ⟨1, by omega⟩
  let u : Fin n := ⟨j.val - 1, by omega⟩
  have hlu : l ≤ u := by change 1 ≤ j.val - 1; omega
  have hc (x : Fin n) (hlx : l ≤ x) (hxu : x ≤ u) : l ≤ m x ∧ m x ≤ u := by
    have hzx : z < x := by change 1 ≤ x.val at hlx; omega
    have hxj : x < j := by change x.val ≤ j.val - 1 at hxu; omega
    obtain ⟨ha, hb⟩ := hm.mate_mem_Ioo hpair hzx hxj
    change 1 ≤ (m x).val ∧ (m x).val ≤ j.val - 1
    omega
  obtain ⟨a, b, ha, hb, hab, hmab⟩ := hm.exists_adjacent_interval l u hlu hc
  refine ⟨a, b, ?_, ?_, hab, hmab⟩
  · change 1 ≤ a.val at ha
    omega
  · change b.val ≤ j.val - 1 at hb
    omega

private theorem exists_adjacent_after {z j : Fin n} (hz : z.val = 0)
    (hpair : m z = j) (hj : j.val + 1 < n) :
    ∃ a b : Fin n, j < a ∧ a.val + 1 = b.val ∧ m a = b := by
  let l : Fin n := ⟨j.val + 1, hj⟩
  let u : Fin n := ⟨n - 1, by omega⟩
  have hlu : l ≤ u := by change j.val + 1 ≤ n - 1; omega
  have hc (x : Fin n) (hlx : l ≤ x) (_ : x ≤ u) : l ≤ m x ∧ m x ≤ u := by
    have hjx : j < x := by change j.val + 1 ≤ x.val at hlx; omega
    have h := hm.mate_gt_right hz hpair hjx
    have hbound := (m x).isLt
    change j.val + 1 ≤ (m x).val ∧ (m x).val ≤ n - 1
    omega
  obtain ⟨a, b, ha, _, hab, hmab⟩ := hm.exists_adjacent_interval l u hlu hc
  refine ⟨a, b, ?_, hab, hmab⟩
  change j.val + 1 ≤ a.val at ha
  omega

omit hm in
private theorem rotate_eq_of_val_add_one {a b : Fin n} (hab : a.val + 1 = b.val) :
    finRotate n a = b := by
  cases n with
  | zero => exact a.elim0
  | succ k =>
    have ha : a ≠ Fin.last k := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_last] at hh
      have hb := b.isLt
      omega
    exact Fin.ext ((coe_finRotate_of_ne_last ha).trans hab)

omit hm in
private theorem rotate_last_eq_zero {a z : Fin n} (ha : a.val + 1 = n)
    (hz : z.val = 0) : finRotate n a = z := by
  cases n with
  | zero => exact a.elim0
  | succ k =>
    have heq : a = Fin.last k :=
      Fin.ext (by simpa only [Fin.val_last] using Nat.add_right_cancel ha)
    rw [heq, finRotate_last]
    exact Fin.ext hz.symm

theorem exists_adjacent (hn : 0 < n) :
    ∃ a b : Fin n, a.val + 1 = b.val ∧ m a = b := by
  let z : Fin n := ⟨0, hn⟩
  let u : Fin n := ⟨n - 1, by omega⟩
  have hzu : z ≤ u := by change 0 ≤ n - 1; omega
  have hc (x : Fin n) (_ : z ≤ x) (_ : x ≤ u) : z ≤ m x ∧ m x ≤ u := by
    have h := (m x).isLt
    change 0 ≤ (m x).val ∧ (m x).val ≤ n - 1
    omega
  obtain ⟨a, b, _, _, hab, hmab⟩ := hm.exists_adjacent_interval z u hzu hc
  exact ⟨a, b, hab, hmab⟩

theorem exists_adjacent_away_first (hn : 4 ≤ n) :
    ∃ a b : Fin n, 0 < a.val ∧ a.val + 1 = b.val ∧ m a = b := by
  let z : Fin n := ⟨0, by omega⟩
  let j := m z
  have hj : 0 < j.val := by
    have h := hm.ne_self z
    have hne : j.val ≠ 0 := fun hh => h (Fin.ext hh)
    omega
  by_cases hj1 : j.val = 1
  · obtain ⟨a, b, hja, hab, hmab⟩ :=
      hm.exists_adjacent_after (z := z) rfl (show m z = j from rfl) (by omega)
    exact ⟨a, b, by omega, hab, hmab⟩
  · obtain ⟨a, b, ha, _, hab, hmab⟩ :=
      hm.exists_adjacent_before (z := z) rfl (show m z = j from rfl) (by omega)
    exact ⟨a, b, ha, hab, hmab⟩

theorem exists_two_cyclic_adjacent (hn : 4 ≤ n) :
    ∃ a b : Fin n, m a = finRotate n a ∧ m b = finRotate n b ∧
      Disjoint ({a, finRotate n a} : Set (Fin n)) {b, finRotate n b} := by
  let z : Fin n := ⟨0, by omega⟩
  have hz : z.val = 0 := rfl
  let j := m z
  have hj : 0 < j.val := by
    have h := hm.ne_self z
    have hne : j.val ≠ 0 := fun hh => h (Fin.ext hh)
    omega
  have hjn : j.val < n := j.isLt
  have hmj : m j = z := hm.involutive z
  by_cases hj1 : j.val = 1
  · obtain ⟨a, b, hja, hab, hmab⟩ :=
      hm.exists_adjacent_after (z := z) rfl (show m z = j from rfl) (by omega)
    have hzrot : finRotate n z = j := rotate_eq_of_val_add_one (by change 0 + 1 = j.val; omega)
    have harot : finRotate n a = b := rotate_eq_of_val_add_one hab
    refine ⟨z, a, hzrot.symm, hmab.trans harot.symm, ?_⟩
    rw [hzrot, harot]
    apply Set.disjoint_left.mpr
    rintro x (rfl | rfl) (h | h) <;> change _ = _ at h <;> omega
  · by_cases hjlast : j.val + 1 = n
    · obtain ⟨a, b, ha, hbj, hab, hmab⟩ :=
        hm.exists_adjacent_before (z := z) rfl (show m z = j from rfl) (by omega)
      have hjrot : finRotate n j = z := rotate_last_eq_zero hjlast rfl
      have harot : finRotate n a = b := rotate_eq_of_val_add_one hab
      refine ⟨j, a, hmj.trans hjrot.symm, hmab.trans harot.symm, ?_⟩
      rw [hjrot, harot]
      apply Set.disjoint_left.mpr
      rintro x (rfl | rfl) (h | h) <;> change _ = _ at h <;> omega
    · obtain ⟨a, b, _, hbj, hab, hmab⟩ :=
        hm.exists_adjacent_before (z := z) rfl (show m z = j from rfl) (by omega)
      obtain ⟨c, d, hjc, hcd, hmcd⟩ :=
        hm.exists_adjacent_after (z := z) rfl (show m z = j from rfl) (by omega)
      have harot : finRotate n a = b := rotate_eq_of_val_add_one hab
      have hcrot : finRotate n c = d := rotate_eq_of_val_add_one hcd
      refine ⟨a, c, hmab.trans harot.symm, hmcd.trans hcrot.symm, ?_⟩
      rw [harot, hcrot]
      apply Set.disjoint_left.mpr
      rintro x (rfl | rfl) (h | h) <;> change _ = _ at h <;> omega

theorem exists_cyclic_adjacent_away (hn : 4 ≤ n) (v : Fin n) :
    ∃ a : Fin n, m a = finRotate n a ∧ a ≠ v ∧ finRotate n a ≠ v := by
  obtain ⟨a, b, ha, hb, hd⟩ := hm.exists_two_cyclic_adjacent hn
  by_cases hv : v ∈ ({a, finRotate n a} : Set (Fin n))
  · refine ⟨b, hb, ?_, ?_⟩
    · intro h
      exact Set.disjoint_left.mp hd hv (Or.inl h.symm)
    · intro h
      exact Set.disjoint_left.mp hd hv (Or.inr h.symm)
  · refine ⟨a, ha, ?_, ?_⟩
    · intro h
      exact hv (Or.inl h.symm)
    · intro h
      exact hv (Or.inr h.symm)

end IsNoninterlacingMatching

end PoincareConjecture.M25.Topology3D
