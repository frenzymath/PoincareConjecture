import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc










set_option autoImplicit false

open Set

namespace AddCircle

open Classical in



theorem signed_phase_arc_membership (p : ℝ) [Fact (0 < p)]
    {a b r rho t : ℝ} (hr : 0 ≤ r)
    (ha : 0 < a - r) (hab : a + r < b - r) (hb : b + r < p)
    (hrho : rho ≤ r) (ht : t ∈ Icc (-r) r)
    {v : AddCircle p} (hv : v ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set _)) :
    (v + (((if v = (a : AddCircle p) then 1 else -1) * t : ℝ) : AddCircle p) ∈
        closedIntervalArc p (a - rho) (a + rho) ↔
      v = (a : AddCircle p) ∧ t ∈ Icc (-rho) rho) ∧
    (v + (((if v = (a : AddCircle p) then 1 else -1) * t : ℝ) : AddCircle p) ∈
        closedIntervalArc p (b - rho) (b + rho) ↔
      v = (b : AddCircle p) ∧ t ∈ Icc (-rho) rho) := by
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := by constructor <;> linarith
  have habNe : (a : AddCircle p) ≠ (b : AddCircle p) := by
    intro heq
    have habEq := (coe_eq_coe_iff_of_mem_Ico haI hbI).mp heq
    linarith
  have haLower : 0 ≤ a - rho := by linarith
  have haUpper : a + rho < p := by linarith
  have hbLower : 0 ≤ b - rho := by linarith
  have hbUpper : b + rho < p := by linarith
  simp only [mem_insert_iff, mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · have hu : a + t ∈ Ico (0 : ℝ) p := by constructor <;> linarith [ht.1, ht.2]
    have hformula : (a : AddCircle p) +
        (((if (a : AddCircle p) = (a : AddCircle p) then 1 else -1) * t : ℝ) :
          AddCircle p) = ((a + t : ℝ) : AddCircle p) := by
      simp only [if_true, one_mul, coe_add]
    rw [hformula]
    constructor
    · rw [coe_mem_closedIntervalArc_iff p haLower haUpper hu]
      constructor
      · intro h
        exact ⟨rfl, by constructor <;> linarith [h.1, h.2]⟩
      · rintro ⟨_, h⟩
        constructor <;> linarith [h.1, h.2]
    · apply iff_of_false
      · intro h
        have hreal := (coe_mem_closedIntervalArc_iff p hbLower hbUpper hu).mp h
        linarith [hreal.1, ht.2]
      · exact fun h => habNe h.1
  · have hu : b - t ∈ Ico (0 : ℝ) p := by constructor <;> linarith [ht.1, ht.2]
    have hformula : (b : AddCircle p) +
        (((if (b : AddCircle p) = (a : AddCircle p) then 1 else -1) * t : ℝ) :
          AddCircle p) = ((b - t : ℝ) : AddCircle p) := by
      simp only [if_neg habNe.symm, neg_one_mul, sub_eq_add_neg, coe_add]
    rw [hformula]
    constructor
    · apply iff_of_false
      · intro h
        have hreal := (coe_mem_closedIntervalArc_iff p haLower haUpper hu).mp h
        linarith [hreal.2, ht.2]
      · exact fun h => habNe.symm h.1
    · rw [coe_mem_closedIntervalArc_iff p hbLower hbUpper hu]
      constructor
      · intro h
        exact ⟨rfl, by constructor <;> linarith [h.1, h.2]⟩
      · rintro ⟨_, h⟩
        constructor <;> linarith [h.1, h.2]

end AddCircle
