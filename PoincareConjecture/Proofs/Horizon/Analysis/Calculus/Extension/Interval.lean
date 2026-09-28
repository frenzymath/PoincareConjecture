


import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.Local







set_option autoImplicit false
open Set Metric Filter
open scoped ContDiff Topology

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem exists_global_contDiff_near_interval {f : ℝ → E} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {a b : ℝ}
    (hab : a ≤ b) (hI : Icc a b ⊆ U) :
    ∃ (g : ℝ → E) (l r : ℝ), ContDiff ℝ ∞ g ∧
      l < a ∧ b < r ∧ Ioo l r ⊆ U ∧ EqOn g f (Ioo l r) := by
  obtain ⟨l₀, l', hl, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hI (left_mem_Icc.mpr hab)))
  obtain ⟨r', r₀, hr, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hI (right_mem_Icc.mpr hab)))
  have hwide : Ioo l₀ r₀ ⊆ U := by
    intro x hx
    by_cases hxa : x < a
    · exact hleft ⟨hx.1, hxa.trans hl.2⟩
    by_cases hbx : b < x
    · exact hright ⟨hr.1.trans hbx, hx.2⟩
    exact hI ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩
  let η := min (a - l₀) (r₀ - b) / 4
  have hη : 0 < η := div_pos (lt_min (sub_pos.mpr hl.1) (sub_pos.mpr hr.2)) (by norm_num)
  have hηl : 4 * η ≤ a - l₀ := by dsimp [η]; linarith [min_le_left (a - l₀) (r₀ - b)]
  have hηr : 4 * η ≤ r₀ - b := by dsimp [η]; linarith [min_le_right (a - l₀) (r₀ - b)]
  let c := (a + b) / 2
  let χ : ContDiffBump c := {
    rIn := (b - a) / 2 + η
    rOut := (b - a) / 2 + 2 * η
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  have hsupport : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro x hx
    have hd : |x - c| ≤ (b - a) / 2 + 2 * η := by
      simpa only [mem_closedBall, Real.dist_eq] using hx
    obtain ⟨hxl, hxr⟩ := abs_le.mp hd
    apply hwide
    dsimp [c] at hxl hxr
    constructor <;> linarith
  refine ⟨fun x => χ x • f x, a - η, b + η, ?_, by linarith, by linarith, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact χ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun hx' => hx (hsupport hx')
      apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp [hy]
  · intro x hx
    apply hwide
    constructor <;> linarith [hx.1, hx.2]
  · intro x hx
    dsimp only
    rw [χ.one_of_mem_closedBall, one_smul]
    rw [mem_closedBall, Real.dist_eq]
    change |x - c| ≤ (b - a) / 2 + η
    rw [abs_le]
    dsimp [c]
    constructor <;> linarith [hx.1, hx.2]

end Poincare.Analysis
