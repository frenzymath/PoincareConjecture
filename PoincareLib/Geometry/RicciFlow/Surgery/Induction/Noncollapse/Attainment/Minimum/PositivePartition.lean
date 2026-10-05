import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Minimization.Charts.PathGluing

/-!
# Nondegenerate pieces of the action partition

Proposition 16.4, p. 369. Only positive-length pieces are needed for
recovery gluing. They still cover the full interval, and distinct pieces
can meet only at an interior endpoint. The original action sum is retained.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.Proofs.M46

/-- Removing zero-length pieces retains a closed cover of every
nondegenerate parameter interval. Source: the finite subdivision in
the direct method of Proposition 16.4, p. 369. -/
theorem positive_partition_covers {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hab : t 0 < t (Fin.last m)) {s : ℝ} (hs : s ∈ Icc (t 0) (t (Fin.last m))) :
    ∃ i : Fin m, t i.castSucc < t i.succ ∧ s ∈ Icc (t i.castSucc) (t i.succ) := by
  induction m with
  | zero => simp at hab
  | succ m ih =>
    let c := t (Fin.last m).castSucc
    have hac : t 0 ≤ c := ht (Fin.zero_le _)
    by_cases hsc : s ≤ c
    · by_cases hac' : t 0 < c
      · obtain ⟨i, hi, hsi⟩ := ih (fun j => t j.castSucc)
          (fun _ _ hj => ht hj) hac' ⟨hs.1, hsc⟩
        exact ⟨i.castSucc, hi, hsi⟩
      · have hca : c = t 0 := le_antisymm (le_of_not_gt hac') hac
        have hcs : c ≤ s := hca ▸ hs.1
        exact ⟨Fin.last m, hca.le.trans_lt hab, hcs, hs.2⟩
    · exact ⟨Fin.last m, (lt_of_not_ge hsc).trans_le hs.2,
        (lt_of_not_ge hsc).le, hs.2⟩

/-- Ordered distinct positive pieces meet at their adjacent endpoint,
which is strictly inside the global interval. Source: the recovery
subdivision in Proposition 16.4, p. 369. -/
theorem positive_partition_intersection {m : ℕ} (t : Fin (m + 1) → ℝ)
    (ht : Monotone t) {i j : Fin m} (hij : i < j)
    (hi : t i.castSucc < t i.succ) (hj : t j.castSucc < t j.succ)
    {s : ℝ} (hsi : s ∈ Icc (t i.castSucc) (t i.succ))
    (hsj : s ∈ Icc (t j.castSucc) (t j.succ)) :
    s = t i.succ ∧ s = t j.castSucc ∧ s ∈ Ioo (t 0) (t (Fin.last m)) := by
  have horder : t i.succ ≤ t j.castSucc := ht (by
    change i.val + 1 ≤ j.val
    exact Nat.succ_le_of_lt hij)
  have hright : s = t i.succ := le_antisymm hsi.2 (horder.trans hsj.1)
  have hleft : s = t j.castSucc := le_antisymm (hsi.2.trans horder) hsj.1
  refine ⟨hright, hleft, ?_, ?_⟩
  · rw [hright]
    exact (ht (Fin.zero_le _)).trans_lt hi
  · rw [hleft]
    exact hj.trans_le (ht (Fin.le_last _))

/-- A partition node lying in a positive piece is one of that piece's
endpoints. This recovers values at omitted zero-length pieces. Source:
the finite subdivision in Proposition 16.4, p. 369. -/
theorem partition_node_endpoint {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (k : Fin (m + 1)) (i : Fin m) (hk : t k ∈ Icc (t i.castSucc) (t i.succ)) :
    t k = t i.castSucc ∨ t k = t i.succ := by
  by_cases hki : k ≤ i.castSucc
  · exact Or.inl (le_antisymm (ht hki) hk.1)
  · have hik : i.succ ≤ k := by
      change i.val + 1 ≤ k.val
      have hh : ¬ k.val ≤ i.val := hki
      exact Nat.succ_le_of_lt (lt_of_not_ge hh)
    exact Or.inr (le_antisymm hk.2 (ht hik))

end PoincareMT.Proofs.M46
