import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false

open Set

namespace Finset

theorem exists_ordered_partition {α : Type*} [LinearOrder α]
    (T : Finset α) {l u : α} (hlu : l < u) (hT : (T : Set α) ⊆ Set.Icc l u)
    (hl : l ∈ T) (hu : u ∈ T) :
    ∃ (n : ℕ) (t : Fin (n + 2) → α), StrictMono t ∧ t 0 = l ∧
      t (Fin.last (n + 1)) = u ∧ Set.range t = T ∧
      ∀ i : Fin (n + 1), Disjoint (Set.Ioo (t i.castSucc) (t i.succ)) (T : Set α) := by
  classical
  have hcard : 2 ≤ T.card := by
    have hpair : ({l, u} : Finset α) ⊆ T := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hl
      · exact Finset.mem_singleton.mp hx ▸ hu
    have h := Finset.card_le_card hpair
    simpa [hlu.ne] using h
  obtain ⟨n, hn⟩ : ∃ n, T.card = n + 2 := ⟨T.card - 2, by omega⟩
  let t := T.orderEmbOfFin hn
  have hmono : StrictMono t := t.strictMono
  have hrange : Set.range t = T := T.range_orderEmbOfFin hn
  have hmem (i : Fin (n + 2)) : t i ∈ T := T.orderEmbOfFin_mem hn i
  have hfirst : t 0 = l := by
    obtain ⟨i, hi⟩ := hrange.symm ▸ (show l ∈ (T : Set α) from hl)
    exact le_antisymm (hi ▸ hmono.monotone (Fin.zero_le i)) (hT (hmem 0)).1
  have hlast : t (Fin.last (n + 1)) = u := by
    obtain ⟨i, hi⟩ := hrange.symm ▸ (show u ∈ (T : Set α) from hu)
    exact le_antisymm (hT (hmem _)).2 (hi ▸ hmono.monotone (Fin.le_last i))
  refine ⟨n, t, hmono, hfirst, hlast, hrange, fun i => Set.disjoint_left.mpr ?_⟩
  intro x hx hxT
  obtain ⟨j, rfl⟩ := hrange.symm ▸ hxT
  have hleft := hmono.lt_iff_lt.mp hx.1
  have hright := hmono.lt_iff_lt.mp hx.2
  have hvleft : i.val < j.val := hleft
  have hvright : j.val < i.val + 1 := hright
  omega

end Finset

theorem Monotone.exists_mem_consecutive_Icc {α : Type*} [LinearOrder α]
    {n : ℕ} {t : Fin (n + 2) → α} (ht : Monotone t) {x : α}
    (hx : x ∈ Icc (t 0) (t (Fin.last (n + 1)))) :
    ∃ j : Fin (n + 1), x ∈ Icc (t j.castSucc) (t j.succ) := by
  classical
  let H : Finset (Fin (n + 2)) := Finset.univ.filter fun i => t i ≤ x
  have hH : H.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩⟩
  let i := H.max' hH
  have hi : t i ≤ x := (Finset.mem_filter.mp (H.max'_mem hH)).2
  by_cases hilast : i = Fin.last (n + 1)
  · refine ⟨Fin.last n, ?_, hx.2⟩
    exact (ht (Fin.le_last _)).trans (hilast ▸ hi)
  · obtain ⟨j, hj⟩ := Fin.eq_castSucc_of_ne_last hilast
    refine ⟨j, hj ▸ hi, ?_⟩
    by_contra h
    have hmem : j.succ ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_ge h⟩
    have hle : j.succ ≤ i := Finset.le_max' H _ hmem
    have hi' : i = j.castSucc := hj.symm
    rw [hi'] at hle
    exact (not_le_of_gt Fin.castSucc_lt_succ) hle

theorem StrictMono.eq_endpoints_of_mem_consecutive_Icc {α : Type*} [LinearOrder α]
    {n : ℕ} {t : Fin (n + 2) → α} (ht : StrictMono t)
    {j k : Fin (n + 1)} (hjk : j ≠ k) {x : α}
    (hj : x ∈ Icc (t j.castSucc) (t j.succ))
    (hk : x ∈ Icc (t k.castSucc) (t k.succ)) :
    (x = t j.castSucc ∨ x = t j.succ) ∧ (x = t k.castSucc ∨ x = t k.succ) := by
  have hordered {a b : Fin (n + 1)} (hab : a < b)
      (ha : x ∈ Icc (t a.castSucc) (t a.succ))
      (hb : x ∈ Icc (t b.castSucc) (t b.succ)) : x = t a.succ ∧ x = t b.castSucc := by
    have hab' : a.succ ≤ b.castSucc := by
      change a.val + 1 ≤ b.val
      exact Nat.succ_le_of_lt hab
    have hle := ht.monotone hab'
    exact ⟨le_antisymm ha.2 (hle.trans hb.1), le_antisymm (ha.2.trans hle) hb.1⟩
  rcases lt_or_gt_of_ne hjk with h | h
  · obtain ⟨h1, h2⟩ := hordered h hj hk
    exact ⟨Or.inr h1, Or.inl h2⟩
  · obtain ⟨h1, h2⟩ := hordered h hk hj
    exact ⟨Or.inl h2, Or.inr h1⟩
