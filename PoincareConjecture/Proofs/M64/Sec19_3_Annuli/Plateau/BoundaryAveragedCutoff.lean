import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRadialCutoff












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture




def m64BoundaryCutoffRadius (R : ℝ) (j : ℕ) : ℝ := R / 4 ^ j




theorem m64BoundaryCutoffRadius_pos {R : ℝ} (hR : 0 < R) (j : ℕ) :
    0 < m64BoundaryCutoffRadius R j := by unfold m64BoundaryCutoffRadius; positivity




theorem m64BoundaryCutoffRadius_antitone {R : ℝ} (hR : 0 < R) :
    Antitone (m64BoundaryCutoffRadius R) := by
  intro i j hij
  unfold m64BoundaryCutoffRadius
  gcongr
  norm_num




theorem m64BoundaryCutoffRadius_succ (R : ℝ) (j : ℕ) :
    m64BoundaryCutoffRadius R (j + 1) = m64BoundaryCutoffRadius R j / 4 := by
  simp only [m64BoundaryCutoffRadius, pow_succ, div_mul_eq_div_div]




def m64BoundaryAveragedCutoff (a : LoopPlane) (R : ℝ) (N : ℕ) (p : LoopPlane) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
    m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j) p




theorem m64BoundaryAveragedCutoff_contDiff (a : LoopPlane) (R : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (m64BoundaryAveragedCutoff a R N) := by
  apply contDiff_const.mul
  exact ContDiff.sum (fun j _ => m64BoundaryRadialCutoff_contDiff a _)




theorem m64BoundaryAveragedCutoff_nonneg (a : LoopPlane) (R : ℝ) (N : ℕ) (p : LoopPlane) :
    0 ≤ m64BoundaryAveragedCutoff a R N p := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun j _ => m64BoundaryRadialCutoff_nonneg a _ p)




theorem m64BoundaryAveragedCutoff_le_one (a : LoopPlane) (R : ℝ)
    {N : ℕ} (hN : 0 < N) (p : LoopPlane) : m64BoundaryAveragedCutoff a R N p ≤ 1 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hsum : (∑ j ∈ Finset.range N,
      m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j) p) ≤ (N : ℝ) := by
    simpa using Finset.sum_le_sum (s := Finset.range N)
      (g := fun _ => (1 : ℝ)) (fun j _ => m64BoundaryRadialCutoff_le_one a _ p)
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq
    (inv_mul_cancel₀ hn)




theorem m64BoundaryAveragedCutoff_antitone_radius {a p q : LoopPlane} {R : ℝ}
    (hR : 0 < R) (N : ℕ) (hpq : ‖p - a‖ ≤ ‖q - a‖) :
    m64BoundaryAveragedCutoff a R N q ≤ m64BoundaryAveragedCutoff a R N p := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_le_sum (fun j _ =>
    m64BoundaryRadialCutoff_antitone_radius (m64BoundaryCutoffRadius_pos hR j) hpq)




theorem m64BoundaryAveragedCutoff_eq_one {a p : LoopPlane} {R : ℝ}
    (hR : 0 < R) {N : ℕ} (hN : 0 < N)
    (hp : ‖p - a‖ ≤ m64BoundaryCutoffRadius R N / 2) :
    m64BoundaryAveragedCutoff a R N p = 1 := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j) p = 1 := by
    apply m64BoundaryRadialCutoff_eq_one (m64BoundaryCutoffRadius_pos hR j)
    exact hp.trans (div_le_div_of_nonneg_right
      (m64BoundaryCutoffRadius_antitone hR (Nat.le_of_lt (Finset.mem_range.mp hj)))
      (by norm_num))
  simp only [m64BoundaryAveragedCutoff, Finset.sum_congr rfl hterm,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))




theorem m64BoundaryAveragedCutoff_eq_zero {a p : LoopPlane} {R : ℝ}
    (hR : 0 < R) (N : ℕ) (hp : R ≤ ‖p - a‖) :
    m64BoundaryAveragedCutoff a R N p = 0 := by
  have hterm (j : ℕ) (_hj : j ∈ Finset.range N) :
      m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j) p = 0 := by
    apply m64BoundaryRadialCutoff_eq_zero (m64BoundaryCutoffRadius_pos hR j)
    have hj := m64BoundaryCutoffRadius_antitone hR (Nat.zero_le j)
    simp only [m64BoundaryCutoffRadius, pow_zero, div_one] at hj
    exact hj.trans hp
  simp only [m64BoundaryAveragedCutoff, Finset.sum_congr rfl hterm,
    Finset.sum_const_zero, mul_zero]




theorem m64BoundaryAveragedCutoff_column (a p : LoopPlane) (R : ℝ) (N : ℕ) (i : Fin 2) :
    fderiv ℝ (m64BoundaryAveragedCutoff a R N) p (EuclideanSpace.single i 1) =
      (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
        fderiv ℝ (m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j)) p
          (EuclideanSpace.single i 1) := by
  have hd (j : ℕ) : DifferentiableAt ℝ
      (m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j)) p :=
    (m64BoundaryRadialCutoff_contDiff a _).differentiable (by simp) p
  unfold m64BoundaryAveragedCutoff
  rw [fderiv_const_mul (DifferentiableAt.fun_sum (fun j _ => hd j)),
    fderiv_fun_sum (fun j _ => hd j)]
  simp

private theorem cutoff_columns_mul_eq_zero {a p : LoopPlane} {R : ℝ}
    (hR : 0 < R) {j k : ℕ} (hjk : j < k) (i : Fin 2) :
    fderiv ℝ (m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j)) p
        (EuclideanSpace.single i 1) *
      fderiv ℝ (m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R k)) p
        (EuclideanSpace.single i 1) = 0 := by
  by_cases hp : ‖p - a‖ ≤ m64BoundaryCutoffRadius R j / 2
  · rw [m64BoundaryRadialCutoff_fderiv_eq_zero (m64BoundaryCutoffRadius_pos hR j)
      (Or.inl hp)]
    simp
  · have hjk' := m64BoundaryCutoffRadius_antitone hR (Nat.succ_le_of_lt hjk)
    rw [m64BoundaryCutoffRadius_succ] at hjk'
    have hzero := m64BoundaryRadialCutoff_fderiv_eq_zero
      (m64BoundaryCutoffRadius_pos hR k) (p := p) (Or.inr (by
        linarith [m64BoundaryCutoffRadius_pos hR j]))
    rw [hzero]
    simp

private theorem sq_sum_of_pairwise_mul_zero {I : Type*} (s : Finset I) (f : I → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 := by
  classical
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact (pow_two _).symm
  · intro j hj hji
    exact h i hi j hj hji.symm
  · exact fun hnot => (hnot hi).elim





theorem m64BoundaryAveragedCutoff_column_energy (a : LoopPlane) {R : ℝ}
    (hR : 0 < R) {N : ℕ} (hN : 0 < N) (i : Fin 2) :
    (∫ p, (fderiv ℝ (m64BoundaryAveragedCutoff a R N) p
      (EuclideanSpace.single i 1)) ^ 2) =
      (∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p
        (EuclideanSpace.single i 1)) ^ 2) / N := by
  have hpoint (p : LoopPlane) :
      (fderiv ℝ (m64BoundaryAveragedCutoff a R N) p (EuclideanSpace.single i 1)) ^ 2 =
      (N : ℝ)⁻¹ ^ 2 * ∑ j ∈ Finset.range N,
        (fderiv ℝ (m64BoundaryRadialCutoff a (m64BoundaryCutoffRadius R j)) p
          (EuclideanSpace.single i 1)) ^ 2 := by
    rw [m64BoundaryAveragedCutoff_column, mul_pow]
    congr 1
    apply sq_sum_of_pairwise_mul_zero
    intro j _ k _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact cutoff_columns_mul_eq_zero hR h i
    · rw [mul_comm]
      exact cutoff_columns_mul_eq_zero hR h i
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ =>
    m64BoundaryRadialCutoff_column_integrable a (m64BoundaryCutoffRadius_pos hR j) i)]
  simp_rw [m64BoundaryRadialCutoff_column_energy a (m64BoundaryCutoffRadius_pos hR _) i]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

end PoincareConjecture
