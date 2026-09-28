import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ProfilePrimitive

set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture

theorem m63Flattening_int_cell_shift {N : ℕ} (hN : 0 < N) (x : ℝ) (j : ℤ) :
    m63Flattening N (x + (j : ℝ) * m63CellLength N) =
      m63Flattening N x + (j : ℝ) * m63CellLength N := by
  have hp : Function.Periodic (fun y => m63Flattening N y - y) (m63CellLength N) := by
    intro y
    change m63Flattening N (y + m63CellLength N) - (y + m63CellLength N) =
      m63Flattening N y - y
    rw [m63Flattening_cell_shift hN]
    ring
  have h := hp.int_mul j x
  linarith

theorem m63Flattening_vertex {N : ℕ} (hN : 0 < N) (j : ℤ) :
    m63Flattening N ((j : ℝ) * m63CellLength N) = (j : ℝ) * m63CellLength N := by
  simpa only [zero_add, m63Flattening_zero] using m63Flattening_int_cell_shift hN 0 j

theorem m63Flattening_flat {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : 0 < i) (j : ℤ) :
    iteratedDeriv i (m63Flattening N) ((j : ℝ) * m63CellLength N) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  rw [iteratedDeriv_succ']
  have hd : deriv (m63Flattening N) = m63Profile N :=
    funext fun x => (m63Flattening_hasDerivAt N x).deriv
  rw [hd]
  exact m63Profile_flat hN k j

theorem m63Flattening_mem_cell {N : ℕ} (hN : 0 < N) (j : ℤ) {s : ℝ}
    (hs : s ∈ Set.Icc 0 (m63CellLength N)) :
    m63Flattening N ((j : ℝ) * m63CellLength N + s) - (j : ℝ) * m63CellLength N ∈
      Set.Icc 0 (m63CellLength N) := by
  rw [add_comm ((j : ℝ) * m63CellLength N) s,
    m63Flattening_int_cell_shift hN, add_sub_cancel_right]
  have hleft := (m63Flattening_strictMono hN).monotone hs.1
  have hright := (m63Flattening_strictMono hN).monotone hs.2
  have hend : m63Flattening N (m63CellLength N) = m63CellLength N := by
    simpa only [Int.cast_one, one_mul] using m63Flattening_vertex hN 1
  exact ⟨by simpa only [m63Flattening_zero] using hleft, by simpa only [hend] using hright⟩

theorem m63Flattening_mem_open_cell {N : ℕ} (hN : 0 < N) (j : ℤ) {s : ℝ}
    (hs : s ∈ Set.Ioo 0 (m63CellLength N)) :
    m63Flattening N ((j : ℝ) * m63CellLength N + s) - (j : ℝ) * m63CellLength N ∈
      Set.Ioo 0 (m63CellLength N) := by
  rw [add_comm ((j : ℝ) * m63CellLength N) s,
    m63Flattening_int_cell_shift hN, add_sub_cancel_right]
  have hleft := m63Flattening_strictMono hN hs.1
  have hright := m63Flattening_strictMono hN hs.2
  have hend : m63Flattening N (m63CellLength N) = m63CellLength N := by
    simpa only [Int.cast_one, one_mul] using m63Flattening_vertex hN 1
  exact ⟨by simpa only [m63Flattening_zero] using hleft, by simpa only [hend] using hright⟩

end PoincareConjecture
