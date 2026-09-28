import PoincareConjecture.Proofs.M25.Topology3D.Plane.CircleParameter
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_or_endpoints_of_sphereCircleParameter_eq (e : ℂ ≃ₗᵢ[ℝ] E) {a b : ℝ}
    (ha : a ∈ Icc 0 (2 * Real.pi)) (hb : b ∈ Icc 0 (2 * Real.pi))
    (heq : sphereCircleParameter e a = sphereCircleParameter e b) :
    a = b ∨ (a = 0 ∧ b = 2 * Real.pi) ∨ (a = 2 * Real.pi ∧ b = 0) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have h0 : (0 : ℝ) ∈ Ico 0 (2 * Real.pi) := ⟨le_rfl, hp⟩
  have hinj := injOn_sphereCircleParameter_Ico e (a := 0) (b := 2 * Real.pi)
    (by simp)
  have hperiod := (periodic_sphereCircleParameter e).eq
  by_cases hat : a = 2 * Real.pi
  · by_cases hbt : b = 2 * Real.pi
    · exact Or.inl (hat.trans hbt.symm)
    · have hb' : b ∈ Ico 0 (2 * Real.pi) :=
        ⟨hb.1, lt_of_le_of_ne hb.2 hbt⟩
      have hbeq : sphereCircleParameter e b = sphereCircleParameter e 0 := by
        rw [← heq, hat, hperiod]
      exact Or.inr (Or.inr ⟨hat, hinj hb' h0 hbeq⟩)
  · have ha' : a ∈ Ico 0 (2 * Real.pi) :=
      ⟨ha.1, lt_of_le_of_ne ha.2 hat⟩
    by_cases hbt : b = 2 * Real.pi
    · have haeq : sphereCircleParameter e a = sphereCircleParameter e 0 := by
        rw [heq, hbt, hperiod]
      exact Or.inr (Or.inl ⟨hinj ha' h0 haeq, hbt⟩)
    · exact Or.inl (hinj ha' ⟨hb.1, lt_of_le_of_ne hb.2 hbt⟩ heq)

theorem injOn_sphereCircleParameter_Icc (e : ℂ ≃ₗᵢ[ℝ] E) {a b : ℝ}
    (hab : b - a < 2 * Real.pi) : InjOn (sphereCircleParameter e) (Icc a b) := by
  apply (injOn_sphereCircleParameter_Ico e (a := a) (b := a + 2 * Real.pi)
    (by linarith)).mono
  intro x hx
  exact ⟨hx.1, by linarith [hx.2]⟩

theorem eq_endpoints_of_mem_adjacent_mesh_intervals {n : ℕ} {s : Fin (n + 1) → ℝ}
    (hs : StrictMono s) {i j : Fin n} (hij : i ≠ j) {x : ℝ}
    (hi : x ∈ Icc (s i.castSucc) (s i.succ))
    (hj : x ∈ Icc (s j.castSucc) (s j.succ)) :
    (x = s i.castSucc ∨ x = s i.succ) ∧
      (x = s j.castSucc ∨ x = s j.succ) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hidx : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact Nat.succ_le_of_lt hij
    have h := hs.monotone hidx
    exact ⟨Or.inr (by linarith [hi.2, hj.1]), Or.inl (by linarith [hi.2, hj.1])⟩
  · have hidx : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact Nat.succ_le_of_lt hji
    have h := hs.monotone hidx
    exact ⟨Or.inl (by linarith [hj.2, hi.1]), Or.inr (by linarith [hj.2, hi.1])⟩

theorem exists_mem_adjacent_mesh_interval {n : ℕ} (hn : 0 < n)
    (s : Fin (n + 1) → ℝ) {x : ℝ} (hx : x ∈ Icc (s 0) (s (Fin.last n))) :
    ∃ i : Fin n, x ∈ Icc (s i.castSucc) (s i.succ) := by
  classical
  have hex : ∃ i : Fin n, x ≤ s i.succ := by
    let i : Fin n := ⟨n - 1, by omega⟩
    have hi : i.succ = Fin.last n := by
      apply Fin.ext
      change n - 1 + 1 = n
      omega
    exact ⟨i, by simpa only [hi] using hx.2⟩
  let j := Fin.find (fun i : Fin n => x ≤ s i.succ) hex
  refine ⟨j, ?_, Fin.find_spec hex⟩
  by_cases hj : j.val = 0
  · have hzero : j.castSucc = 0 := Fin.ext hj
    simpa only [hzero] using hx.1
  · let k : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hkj : k < j := by
      change j.val - 1 < j.val
      omega
    have hpred : k.succ = j.castSucc := by
      apply Fin.ext
      change j.val - 1 + 1 = j.val
      omega
    have hnot := Fin.find_min hex hkj
    rw [hpred] at hnot
    exact (lt_of_not_ge hnot).le

end PoincareConjecture.M25.Topology3D
