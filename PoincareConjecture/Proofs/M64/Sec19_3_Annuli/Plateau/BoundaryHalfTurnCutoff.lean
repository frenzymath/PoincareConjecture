import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnMeasure
import Mathlib.Analysis.SpecialFunctions.SmoothTransition







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture




theorem m64SmoothTransition_deriv_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · apply IsLocalMin.deriv_eq_zero
    filter_upwards [] with y
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  · apply IsLocalMax.deriv_eq_zero
    filter_upwards [] with y
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y




theorem m64SmoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hB x hx).trans (le_max_left _ _)
  · have hz : x ≤ 0 ∨ 1 ≤ x := by simp only [mem_Icc, not_and_or, not_le] at hx; grind
    rw [m64SmoothTransition_deriv_zero hz, abs_zero]
    exact le_max_right _ _




def m64HalfTurnCutoff (j : ℕ) (p : LoopPlane) : ℝ :=
  Real.smoothTransition (((j : ℝ) + 1) / (curvePeriod / 2) * (p 0 - curvePeriod / 2))



theorem m64HalfTurnCutoff_contDiff (j : ℕ) : ContDiff ℝ ∞ (m64HalfTurnCutoff j) := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.mul
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.sub contDiff_const)




theorem m64HalfTurnCutoff_bounds (j : ℕ) (p : LoopPlane) :
    0 ≤ m64HalfTurnCutoff j p ∧ m64HalfTurnCutoff j p ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩




theorem m64HalfTurnCutoff_endpoints (j : ℕ) (s : ℝ) :
    m64HalfTurnCutoff j (annulusPoint 0 s) = 0 ∧
      m64HalfTurnCutoff j (annulusPoint curvePeriod s) = 1 := by
  have ha : 0 < curvePeriod / 2 := by unfold curvePeriod; positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  constructor
  · apply Real.smoothTransition.zero_of_nonpos
    change ((j : ℝ) + 1) / (curvePeriod / 2) * (0 - curvePeriod / 2) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos (div_pos hj ha).le (by linarith)
  · apply Real.smoothTransition.one_of_one_le
    change 1 ≤ ((j : ℝ) + 1) / (curvePeriod / 2) * (curvePeriod - curvePeriod / 2)
    have he : curvePeriod - curvePeriod / 2 = curvePeriod / 2 := by ring
    rw [he, div_mul_cancel₀ _ ha.ne']
    linarith [Nat.cast_nonneg (α := ℝ) j]




theorem m64HalfTurnCutoff_fderiv (j : ℕ) (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (m64HalfTurnCutoff j) p (EuclideanSpace.single i 1) =
      if i = 0 then ((j : ℝ) + 1) / (curvePeriod / 2) *
        deriv Real.smoothTransition
          (((j : ℝ) + 1) / (curvePeriod / 2) * (p 0 - curvePeriod / 2)) else 0 := by
  let c := ((j : ℝ) + 1) / (curvePeriod / 2)
  let L : LoopPlane →L[ℝ] ℝ := c • EuclideanSpace.proj (𝕜 := ℝ) 0
  have hF : HasFDerivAt (fun p : LoopPlane => c * (p 0 - curvePeriod / 2)) L p := by
    simpa only [L, sub_mul, mul_sub, EuclideanSpace.coe_proj] using
      (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.sub_const
        (curvePeriod / 2)).const_mul c)
  have hd := ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable
    (by simp) _).hasDerivAt.comp_hasFDerivAt p hF
  change fderiv ℝ (Real.smoothTransition ∘
    (fun q : LoopPlane => c * (q 0 - curvePeriod / 2))) p _ = _
  rw [hd.fderiv]
  fin_cases i <;> simp [L, c, mul_comm]




theorem m64HalfTurnCutoff_eventually {p : LoopPlane} (hp : p 0 ≠ curvePeriod / 2) :
    ∀ᶠ j : ℕ in atTop,
      m64HalfTurnCutoff j p = if p 0 < curvePeriod / 2 then 0 else 1 := by
  have ha : 0 < curvePeriod / 2 := by unfold curvePeriod; positivity
  rcases lt_or_gt_of_ne hp with hl | hr
  · filter_upwards [] with j
    rw [if_pos hl]
    apply Real.smoothTransition.zero_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hl.le)
  · obtain ⟨N, hN⟩ := exists_nat_gt ((curvePeriod / 2) / (p 0 - curvePeriod / 2))
    have hN' := (div_lt_iff₀ (sub_pos.mpr hr)).mp hN
    filter_upwards [eventually_ge_atTop N] with j hj
    rw [if_neg (not_lt.mpr hr.le)]
    apply Real.smoothTransition.one_of_one_le
    change 1 ≤ ((j : ℝ) + 1) / (curvePeriod / 2) * (p 0 - curvePeriod / 2)
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    have hNj : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith




theorem m64HalfTurnCutoff_deriv_eventually {p : LoopPlane}
    (hp : p 0 ≠ curvePeriod / 2) (i : Fin 2) :
    ∀ᶠ j : ℕ in atTop,
      fderiv ℝ (m64HalfTurnCutoff j) p (EuclideanSpace.single i 1) = 0 := by
  filter_upwards [m64HalfTurnCutoff_eventually hp] with j hj
  rw [m64HalfTurnCutoff_fderiv]
  split_ifs with hi
  · have hz : m64HalfTurnCutoff j p = 0 ∨ m64HalfTurnCutoff j p = 1 := by
      rw [hj]
      split_ifs <;> simp
    have harg : ((j : ℝ) + 1) / (curvePeriod / 2) * (p 0 - curvePeriod / 2) ≤ 0 ∨
        1 ≤ ((j : ℝ) + 1) / (curvePeriod / 2) * (p 0 - curvePeriod / 2) := by
      rcases hz with hz | hz
      · exact Or.inl (Real.smoothTransition.zero_iff_nonpos.mp hz)
      · exact Or.inr (Real.smoothTransition.eq_one_iff_one_le.mp hz)
    rw [m64SmoothTransition_deriv_zero harg, mul_zero]
  · rfl




theorem m64HalfTurnCutoff_matching_derivative_bound
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hbound : ∀ x, |deriv Real.smoothTransition x| ≤ C)
    (j : ℕ) (p : LoopPlane) {z : ℝ}
    (hz : |z| ≤ L * |p 0 - curvePeriod / 2|) :
    |fderiv ℝ (m64HalfTurnCutoff j) p (EuclideanSpace.single (0 : Fin 2) 1) * z| ≤
      C * L := by
  let a := curvePeriod / 2
  let c := ((j : ℝ) + 1) / a
  have ha : 0 < a := by dsimp [a]; unfold curvePeriod; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  rw [m64HalfTurnCutoff_fderiv]
  simp only [ite_true]
  change |(c * deriv Real.smoothTransition (c * (p 0 - a))) * z| ≤ C * L
  by_cases hin : c * (p 0 - a) ∈ Ioo (0 : ℝ) 1
  · have hx : 0 ≤ p 0 - a := (pos_of_mul_pos_right hin.1 hc.le).le
    rw [abs_mul, abs_mul, abs_of_pos hc]
    calc
      _ ≤ (c * C) * (L * |p 0 - a|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hbound _) hc.le) hz
          (abs_nonneg _) (mul_nonneg hc.le hC)
      _ = C * L * (c * (p 0 - a)) := by rw [abs_of_nonneg hx]; ring
      _ ≤ C * L := mul_le_of_le_one_right (mul_nonneg hC hL) hin.2.le
  · have hout : c * (p 0 - a) ≤ 0 ∨ 1 ≤ c * (p 0 - a) := by
      simp only [mem_Ioo, not_and_or, not_lt] at hin
      exact hin
    rw [m64SmoothTransition_deriv_zero hout, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg hC hL

end PoincareConjecture
