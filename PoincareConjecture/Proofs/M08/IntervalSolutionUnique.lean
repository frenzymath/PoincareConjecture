import PoincareConjecture.Proofs.M08.IntervalSolutionGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology

namespace PoincareConjecture.M08

theorem exists_mem_finite_interval_core {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = a) (htb : t (Fin.last m) = b) {s : ℝ} (hs : s ∈ Icc a b) :
    ∃ i : Fin m, s ∈ Icc (t i.castSucc) (t i.succ) := by
  have hcover : ∀ k (hk : k ≤ m), ∀ s ∈ Icc a (t ⟨k, Nat.lt_succ_of_le hk⟩),
      ∃ i : Fin m, s ∈ Icc (t i.castSucc) (t i.succ) := by
    intro k
    induction k with
    | zero =>
      intro hk s hs
      have hzero : t (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (m + 1)) = a := hta
      have hsa : s = a := le_antisymm (hzero ▸ hs.2) hs.1
      let i : Fin m := ⟨0, hm⟩
      refine ⟨i, ?_, ?_⟩
      · change t 0 ≤ s
        rw [hta, hsa]
      · rw [hsa]
        exact hta ▸ ht (Fin.zero_le i.succ)
    | succ k ih =>
      intro hk s hs
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      by_cases hsc : s ≤ t ⟨k, Nat.lt_succ_of_le hk'⟩
      · exact ih hk' s ⟨hs.1, hsc⟩
      · let i : Fin m := ⟨k, Nat.lt_of_succ_le hk⟩
        exact ⟨i, (lt_of_not_ge hsc).le, hs.2⟩
  apply hcover m le_rfl s
  change s ∈ Icc a (t (Fin.last m))
  simpa only [htb] using hs

set_option maxHeartbeats 1000000 in
theorem interval_solution_unique_of_cover {X : Type*}
    (Sol : ℝ → ℝ → (ℝ → X) → Prop) (hSol : IntervalSolutionLocality Sol)
    {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (t : Fin (m + 1) → ℝ) (l r : Fin m → ℝ)
    (ht : Monotone t) (hta : t 0 = a) (htb : t (Fin.last m) = b)
    (hpieces : ∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧
      l i ≤ t i.castSucc ∧ t i.succ ≤ r i)
    (hunique : ∀ i {f g : ℝ → X}, Sol (l i) (r i) f → Sol (l i) (r i) g →
      ∀ s ∈ Icc (l i) (r i), f s = g s → EqOn f g (Icc (l i) (r i)))
    {f g : ℝ → X} (hf : Sol a b f) (hg : Sol a b g) (hinit : f a = g a) :
    EqOn f g (Icc a b) := by
  have hstep : ∀ k (hk : k < m), EqOn f g (Icc (l ⟨k, hk⟩) (r ⟨k, hk⟩)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      let i : Fin m := ⟨0, hk⟩
      obtain ⟨hal, hlr, hrb, hlt, htr⟩ := hpieces i
      apply hunique i (hSol.restrict hal hlr hrb hf) (hSol.restrict hal hlr hrb hg)
        (t i.castSucc) ⟨hlt, (ht (show i.castSucc ≤ i.succ from Nat.le_succ i.val)).trans htr⟩
      change f (t 0) = g (t 0)
      rw [hta]
      exact hinit
    | succ k ih =>
      intro hk
      have hk' : k < m := (Nat.lt_succ_self k).trans hk
      let i : Fin m := ⟨k + 1, hk⟩
      let j : Fin m := ⟨k, hk'⟩
      obtain ⟨hal, hlr, hrb, hlt, htr⟩ := hpieces i
      obtain ⟨hjal, hjlr, hjrb, hjlt, hjtr⟩ := hpieces j
      apply hunique i (hSol.restrict hal hlr hrb hf) (hSol.restrict hal hlr hrb hg)
        (t i.castSucc) ⟨hlt, (ht (show i.castSucc ≤ i.succ from Nat.le_succ i.val)).trans htr⟩
      change f (t j.succ) = g (t j.succ)
      exact ih hk' ⟨hjlt.trans (ht (show j.castSucc ≤ j.succ from Nat.le_succ j.val)), hjtr⟩
  intro s hs
  obtain ⟨i, hi⟩ := exists_mem_finite_interval_core hm t ht hta htb hs
  obtain ⟨hal, hlr, hrb, hlt, htr⟩ := hpieces i
  exact hstep i.val i.isLt ⟨hlt.trans hi.1, hi.2.trans htr⟩

end PoincareConjecture.M08
