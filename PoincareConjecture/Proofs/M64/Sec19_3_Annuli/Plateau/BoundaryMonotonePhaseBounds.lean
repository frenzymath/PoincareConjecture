import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakSeamContinuity











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture





theorem m64MonotoneAffinePhase_bound_on_period
    (b : ℝ → ℝ) (hb : Monotone b) {D B : ℝ}
    (hp : ∀ x, b (x + curvePeriod) = b x + D) (hB : |b 0| ≤ B)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod) : |b x| ≤ B + |D| := by
  have hl := hb hx.1
  have hu := hb hx.2
  have heq : b curvePeriod = b 0 + D := by simpa only [zero_add] using hp 0
  have habs := abs_le.mp hB
  rw [abs_le]
  rw [heq] at hu
  constructor <;> linarith [abs_nonneg D, le_abs_self D]





theorem m64MonotoneAffinePhase_locally_bounded
    {I : Type*} (b : I → ℝ → ℝ) (hb : ∀ j, Monotone (b j)) {D B : ℝ}
    (hp : ∀ j x, b j (x + curvePeriod) = b j x + D) (hB : ∀ j, |b j 0| ≤ B) :
    ∀ x : ℝ, ∃ lo hi : ℝ, ∀ j, b j x ∈ Icc lo hi := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hnat (j : I) (k : ℕ) (x : ℝ) :
      b j (x + (k : ℝ) * curvePeriod) = b j x + (k : ℝ) * D := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc, hp, ih]
      ring
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (|x| / curvePeriod)
  have hNx : |x| < (N : ℝ) * curvePeriod := (div_lt_iff₀ hP).mp hN
  have hleft : -(N : ℝ) * curvePeriod ≤ x := by linarith [neg_abs_le x]
  have hright : x ≤ (N : ℝ) * curvePeriod := (le_abs_self x).trans hNx.le
  refine ⟨-B - (N : ℝ) * D, B + (N : ℝ) * D, ?_⟩
  intro j
  have hlo := hb j hleft
  have hhi := hb j hright
  have hshift := hnat j N (-(N : ℝ) * curvePeriod)
  have hzero : -(N : ℝ) * curvePeriod + (N : ℝ) * curvePeriod = 0 := by ring
  rw [hzero] at hshift
  have hshift' : b j ((N : ℝ) * curvePeriod) = b j 0 + (N : ℝ) * D := by
    simpa only [zero_add] using hnat j N 0
  rw [hshift'] at hhi
  have habs := abs_le.mp (hB j)
  constructor <;> linarith

end PoincareConjecture
