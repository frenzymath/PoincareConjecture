import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Set Metric

noncomputable section

namespace PoincareConjecture.Conjugate.Realization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_contDiff_eqOn_of_contDiffOn_Ioo {f : ℝ → E} {a b c d : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f (Ioo a b)) (hac : a < c) (hcd : c ≤ d) (hdb : d < b) :
    ∃ (F : ℝ → E) (V : Set ℝ),
      ContDiff ℝ n F ∧ IsOpen V ∧ Icc c d ⊆ V ∧ V ⊆ Ioo a b ∧ EqOn F f V := by
  classical
  set m : ℝ := (c + d) / 2 with hm
  set h : ℝ := (d - c) / 2 with hh
  have hh0 : 0 ≤ h := by simp only [hh]; linarith
  set ε : ℝ := min (c - a) (b - d) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)

  set χ : ContDiffBump m :=
    { rIn := h + ε / 3
      rOut := h + 2 * ε / 3
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith } with hχ
  have hrIn : χ.rIn = h + ε / 3 := rfl
  have hrOut : χ.rOut = h + 2 * ε / 3 := rfl

  have hIccV : Icc c d ⊆ ball m χ.rIn := by
    intro x hx
    rw [Real.ball_eq_Ioo, hrIn]
    have : m - h = c ∧ m + h = d := by constructor <;> · simp only [hm, hh]; ring
    obtain ⟨hL, hR⟩ := this
    constructor
    · have := hx.1; linarith [hL ▸ (le_refl (m - h))]
    · have := hx.2; linarith [hR ▸ (le_refl (m + h))]

  have htsup : tsupport (χ : ℝ → ℝ) ⊆ Ioo a b := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc, hrOut]
    intro x hx
    have hεa : ε ≤ c - a := min_le_left _ _
    have hεb : ε ≤ b - d := min_le_right _ _
    have hL : m - h = c := by simp only [hm, hh]; ring
    have hR : m + h = d := by simp only [hm, hh]; ring
    constructor
    · have := hx.1; nlinarith [hL]
    · have := hx.2; nlinarith [hR]
  have hVab : ball m χ.rIn ⊆ Ioo a b :=
    (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (le_of_lt χ.rIn_lt_rOut))).trans
      (χ.tsupport_eq ▸ htsup)

  refine ⟨fun x => if x ∈ Ioo a b then χ x • f x else 0, ball m χ.rIn, ?_,
    isOpen_ball, hIccV, hVab, ?_⟩
  ·
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ioo a b
    ·
      have heq : (fun y => if y ∈ Ioo a b then χ y • f y else 0)
          =ᶠ[nhds x] fun y => χ y • f y := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        simp [hy]
      exact (((χ.contDiff (n := n)).contDiffOn.smul hf).contDiffAt
        (isOpen_Ioo.mem_nhds hx)).congr_of_eventuallyEq heq
    ·
      have hxts : x ∉ tsupport (χ : ℝ → ℝ) := fun hc => hx (htsup hc)
      have heq : (fun y => if y ∈ Ioo a b then χ y • f y else 0)
          =ᶠ[nhds x] fun _ => (0 : E) := by
        filter_upwards [(isClosed_tsupport (χ : ℝ → ℝ)).isOpen_compl.mem_nhds hxts]
          with y hy
        by_cases hy' : y ∈ Ioo a b
        · have : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
          simp [hy', this]
        · simp [hy']
      exact contDiffAt_const.congr_of_eventuallyEq heq
  ·
    intro x hx
    have hxab : x ∈ Ioo a b := hVab hx
    have hχ1 : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [hxab, hχ1]

end PoincareConjecture.Conjugate.Realization

end
