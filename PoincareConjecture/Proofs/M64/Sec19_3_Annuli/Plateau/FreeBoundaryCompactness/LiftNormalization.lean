import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryLiftAlgebra













set_option autoImplicit false

noncomputable section

open Set

namespace PoincareConjecture.M64



def normalizedDegreeOneLift (sigma : M64PeriodicDegreeOneLift) :
    M64PeriodicDegreeOneLift where
  map := fun x => sigma.map x - (⌊sigma.map 0 / curvePeriod⌋ : ℤ) * curvePeriod
  monotone := fun x y hxy => sub_le_sub_right (sigma.monotone hxy) _
  period_shift := by intro x; rw [sigma.period_shift]; ring
  lipschitz_constant := sigma.lipschitz_constant
  lipschitz_nonnegative := sigma.lipschitz_nonnegative
  lipschitz_on := by
    intro x y
    convert sigma.lipschitz_on x y using 1
    congr 1
    ring



theorem normalizedDegreeOneLift_zero (sigma : M64PeriodicDegreeOneLift) :
    (normalizedDegreeOneLift sigma).map 0 ∈ Ico (0 : ℝ) curvePeriod := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hlo := (le_div_iff₀ hP).mp (Int.floor_le (sigma.map 0 / curvePeriod))
  have hhi := (div_lt_iff₀ hP).mp (Int.lt_floor_add_one (sigma.map 0 / curvePeriod))
  change 0 ≤ sigma.map 0 - _ ∧ sigma.map 0 - _ < curvePeriod
  constructor <;> linarith



theorem normalizedDegreeOneLift_trace {X : Type*} {c : ℝ → X}
    (hc : Function.Periodic c curvePeriod) (sigma : M64PeriodicDegreeOneLift) :
    c ∘ (normalizedDegreeOneLift sigma).map = c ∘ sigma.map := by
  funext x
  exact hc.sub_int_mul_eq ⌊sigma.map 0 / curvePeriod⌋




theorem monotone_period_shift_bounds
    {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (hm : Monotone f)
    (hp : ∀ x, f (x + P) = f x + P) (hzero : f 0 ∈ Icc 0 P) (x : ℝ) :
    f x ∈ Icc (x - P) (x + 2 * P) := by
  have hperiod : Function.Periodic (fun x => f x - x) P := by
    intro x
    change f (x + P) - (x + P) = f x - x
    rw [hp]
    ring
  have hz (z : ℤ) : f ((z : ℝ) * P) = f 0 + (z : ℝ) * P := by
    have h := hperiod.int_mul_eq z
    linarith
  let z : ℤ := ⌊x / P⌋
  have hlo : (z : ℝ) * P ≤ x := (le_div_iff₀ hP).mp (Int.floor_le (x / P))
  have hhi : x < ((z : ℝ) + 1) * P :=
    (div_lt_iff₀ hP).mp (Int.lt_floor_add_one (x / P))
  have hleft := hm hlo
  rw [hz] at hleft
  have hright := hm hhi.le
  have hznext : f (((z : ℝ) + 1) * P) = f 0 + ((z : ℝ) + 1) * P := by
    simpa only [Int.cast_add, Int.cast_one] using hz (z + 1)
  rw [hznext] at hright
  exact ⟨by linarith [hzero.1], by linarith [hzero.2]⟩



theorem normalizedDegreeOneLift_bounds (sigma : M64PeriodicDegreeOneLift) (x : ℝ) :
    (normalizedDegreeOneLift sigma).map x ∈ Icc (x - curvePeriod) (x + 2 * curvePeriod) :=
  monotone_period_shift_bounds (by unfold curvePeriod; positivity)
    (normalizedDegreeOneLift sigma).monotone (normalizedDegreeOneLift sigma).period_shift
    (Ico_subset_Icc_self (normalizedDegreeOneLift_zero sigma)) x

end PoincareConjecture.M64
