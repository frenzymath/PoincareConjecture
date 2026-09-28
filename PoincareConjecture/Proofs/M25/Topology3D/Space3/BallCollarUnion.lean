import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallCollarMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartUnion
import Mathlib.Analysis.Normed.Module.Normalize

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_uniform_sphere_band {U : Set E} (hU : IsOpen U)
    (hSU : sphere (0 : E) 1 ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ {x : E | |‖x‖ - 1| < ε} ⊆ U := by
  obtain ⟨d, hd, hsub⟩ := (isCompact_sphere (0 : E) 1).exists_thickening_subset_open hU hSU
  refine ⟨min d 1 / 2, by positivity, ?_, ?_⟩
  · have := min_le_right d (1 : ℝ)
    linarith
  · intro x hx
    change |‖x‖ - 1| < min d 1 / 2 at hx
    have hεd : min d 1 / 2 < d := by
      have := min_le_left d (1 : ℝ)
      linarith
    have hε1 : min d 1 / 2 < 1 := by
      have := min_le_right d (1 : ℝ)
      linarith
    have hx0 : x ≠ 0 := by
      intro hz
      simp only [hz, norm_zero, zero_sub, abs_neg, abs_one] at hx
      linarith
    apply hsub
    apply mem_thickening_iff.mpr
    refine ⟨NormedSpace.normalize x,
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx0), ?_⟩
    have hdist : dist x (NormedSpace.normalize x) = |‖x‖ - 1| := by
      calc
        dist x (NormedSpace.normalize x) =
            ‖(‖x‖ - 1) • NormedSpace.normalize x‖ := by
          rw [dist_eq_norm, sub_smul, one_smul, NormedSpace.norm_smul_normalize]
        _ = |‖x‖ - 1| := by
          rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hx0, mul_one]
    rw [hdist]
    exact hx.trans hεd

theorem exists_ball_collar_band (B : BallNeighborhoodChart E E) (f : E → E)
    (hmatch : ∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1), B.chart x = f x) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ball 0 (1 + ε) ⊆ B.chart.source ∧
      ∀ x : E, |‖x‖ - 1| < ε → B.chart x = f x := by
  obtain ⟨U, hU, hSU, hUf⟩ := eventually_nhdsSet_iff_exists.mp hmatch
  obtain ⟨d, hd, hd1, hband⟩ := exists_uniform_sphere_band hU hSU
  obtain ⟨r, hr, hrs⟩ := B.exists_larger_ball
  let ε := min d (r - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεd : ε < d := by
    have := min_le_left d (r - 1)
    dsimp [ε]
    linarith
  have hεr : ε < r - 1 := by
    have := min_le_right d (r - 1)
    dsimp [ε]
    linarith
  refine ⟨ε, hε, hεd.trans hd1, ?_, fun x hx => hUf x (hband (hx.trans hεd))⟩
  exact (ball_subset_ball (by linarith : 1 + ε ≤ r)).trans hrs

theorem exists_ball_outer_collar_union (B : BallNeighborhoodChart E E)
    (R : OpenPartialHomeomorph E E)
    (hRs : R.source = {x | 0 < ‖x‖ ∧ ‖x‖ < 2})
    (hR : ContDiffOn ℝ ∞ R R.source) (hRi : ContDiffOn ℝ ∞ R.symm R.target)
    (hmatch : ∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1), B.chart x = R x)
    (hout : ∀ x ∈ R.source, 1 < ‖x‖ → R x ∉ B.closedRegion) :
    ∃ J : OpenPartialHomeomorph E E,
      J.source = ball 0 2 ∧ ContDiffOn ℝ ∞ J J.source ∧
      ContDiffOn ℝ ∞ J.symm J.target ∧
      J '' ball 0 2 = B.inside ∪ R '' {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ < 2} ∧
      ∀ x : E, 1 ≤ ‖x‖ → ‖x‖ < 2 → J x = R x := by
  obtain ⟨ε, hε, hε1, hBsource, hagree⟩ := exists_ball_collar_band B R hmatch
  let U : Set E := ball 0 (1 + ε)
  let V : Set E := {x | 1 - ε < ‖x‖ ∧ ‖x‖ < 2}
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hVR : V ⊆ R.source := by
    intro x hx
    rw [hRs]
    exact ⟨by linarith [hx.1], hx.2⟩
  let e := B.chart.restrOpen U isOpen_ball
  let f := R.restrOpen V hV
  have hes : e.source = U := inter_eq_right.mpr hBsource
  have hfs : f.source = V := inter_eq_right.mpr hVR
  have heq : EqOn e f (e.source ∩ f.source) := by
    intro x hx
    apply hagree
    have hxU : ‖x‖ < 1 + ε := mem_ball_zero_iff.mp (show x ∈ U from hes ▸ hx.1)
    have hxV : 1 - ε < ‖x‖ := (hfs ▸ hx.2).1
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hcross (x : E) (hx : x ∈ e.source) (y : E) (hy : y ∈ f.source)
      (hxy : e x = f y) : x = y := by
    have hxU : ‖x‖ < 1 + ε := mem_ball_zero_iff.mp (show x ∈ U from hes ▸ hx)
    have hyV : y ∈ V := hfs ▸ hy
    by_cases hy1 : ‖y‖ ≤ 1
    · have hye : y ∈ e.source := by
        rw [hes]
        exact mem_ball_zero_iff.mpr (by linarith)
      apply e.injOn hx hye
      exact hxy.trans (heq ⟨hye, hy⟩).symm
    · have hygt : 1 < ‖y‖ := lt_of_not_ge hy1
      by_cases hx1 : ‖x‖ ≤ 1
      · exact (hout y (hVR hyV) hygt
          ⟨x, mem_closedBall_zero_iff.mpr hx1, hxy⟩).elim
      · have hxgt : 1 < ‖x‖ := lt_of_not_ge hx1
        have hxV : x ∈ V := ⟨by linarith, by linarith⟩
        apply R.injOn (hVR hxV) (hVR hyV)
        exact (hagree x (abs_lt.mpr ⟨by linarith, by linarith⟩)).symm.trans hxy
  have hi : EqOn e.symm f.symm (e.target ∩ f.target) := by
    intro y hy
    exact hcross _ (e.map_target hy.1) _ (f.map_target hy.2)
      ((e.right_inv hy.1).trans (f.right_inv hy.2).symm)
  let J := glueOpenCharts e f heq hi
  have hsource : J.source = ball 0 2 := by
    rw [glueOpenCharts_source, hes, hfs]
    ext x
    change (x ∈ U ∨ x ∈ V) ↔ x ∈ ball (0 : E) 2
    simp only [U, V, mem_ball_zero_iff, mem_ofPred_eq]
    constructor
    · rintro (hx | hx)
      · linarith
      · exact hx.2
    · intro hx
      by_cases hxU : ‖x‖ < 1 + ε
      · exact Or.inl hxU
      · exact Or.inr ⟨by linarith [le_of_not_gt hxU], hx⟩
  have he : ContDiffOn ℝ ∞ e e.source := B.smooth.mono inter_subset_left
  have hei : ContDiffOn ℝ ∞ e.symm e.target := B.smooth_symm.mono inter_subset_left
  have hf : ContDiffOn ℝ ∞ f f.source := hR.mono inter_subset_left
  have hfi : ContDiffOn ℝ ∞ f.symm f.target := hRi.mono inter_subset_left
  have hJleft (x : E) (hx : ‖x‖ < 1) : J x = B.chart x :=
    glueOpenCharts_eqOn_left e f heq hi
      (hes.symm ▸ mem_ball_zero_iff.mpr (by linarith : ‖x‖ < 1 + ε))
  have hJright (x : E) (hx : 1 ≤ ‖x‖) (hx2 : ‖x‖ < 2) : J x = R x :=
    glueOpenCharts_eqOn_right e f heq hi (hfs.symm ▸ ⟨by linarith, hx2⟩)
  refine ⟨J, hsource, glueOpenCharts_contDiffOn e f heq hi he hf,
    glueOpenCharts_symm_contDiffOn e f heq hi hei hfi, ?_, hJright⟩
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hx2 : ‖x‖ < 2 := mem_ball_zero_iff.mp hx
    by_cases hx1 : ‖x‖ < 1
    · left
      rw [hJleft x hx1]
      exact ⟨x, mem_ball_zero_iff.mpr hx1, rfl⟩
    · right
      rw [hJright x (le_of_not_gt hx1) hx2]
      exact ⟨x, ⟨le_of_not_gt hx1, hx2⟩, rfl⟩
  · rintro y (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
      exact ⟨x, mem_ball_zero_iff.mpr (by linarith), hJleft x hx1⟩
    · exact ⟨x, mem_ball_zero_iff.mpr hx.2, hJright x hx.1 hx.2⟩

end PoincareConjecture.M25.Topology3D
