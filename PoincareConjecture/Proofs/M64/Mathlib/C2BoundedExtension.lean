import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded










noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Metric Filter
open scoped Topology ContDiff

namespace PoincareConjecture

private theorem exists_compact_C2_extension {N K : ℕ}
    {h : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K)}
    {a : EuclideanSpace ℝ (Fin N)} (hh : ContDiffAt ℝ 2 h a) :
    ∃ g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K),
      ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      g =ᶠ[𝓝 a] h := by
  obtain ⟨r, hr, hrc⟩ := Metric.mem_nhds_iff.mp (hh.eventually (by norm_num))
  let chi : ContDiffBump a :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g (y : EuclideanSpace ℝ (Fin N)) := chi y • h y
  have hchi : ContDiff ℝ 2 chi := chi.contDiff
  have hg : ContDiff ℝ 2 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ ball a r
    · exact hchi.contDiffAt.smul (hrc hy)
    · have hys : y ∉ tsupport chi := by
        rw [chi.tsupport_eq]
        exact fun h => hy ((closedBall_subset_ball (by dsimp only [chi]; linarith)) h)
      have hz : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hys] with z hz
        change chi z • h z = 0
        simp only [hz, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have hgc : HasCompactSupport g := chi.hasCompactSupport.smul_right
  refine ⟨g, hg, hgc, ?_⟩
  filter_upwards [chi.eventuallyEq_one] with y hy
  change chi y • h y = h y
  simp only [hy, Pi.one_apply, one_smul]

private theorem compact_first_derivative_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ C :=
  (hgc.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv one_ne_zero)

private theorem compact_C2_derivative_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ y, ‖fderiv ℝ g y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ C := by
  have hD : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hDc : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  obtain ⟨C1, hC1⟩ := compact_first_derivative_bound (hg.of_le (by norm_num)) hgc
  obtain ⟨C2, hC2⟩ := compact_first_derivative_bound hD hDc
  refine ⟨max (max C1 C2) 0 + 1, by positivity, ?_⟩
  intro y
  constructor
  · exact (hC1 y).trans (by linarith [le_max_left C1 C2, le_max_left (max C1 C2) 0])
  · exact (hC2 y).trans (by linarith [le_max_right C1 C2, le_max_left (max C1 C2) 0])




theorem m64C2_exists_bounded_extension {N K : ℕ}
    {h : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K)}
    {a : EuclideanSpace ℝ (Fin N)} (hh : ContDiffAt ℝ 2 h a) :
    ∃ (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K)) (C : ℝ),
      0 < C ∧ ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ y, ‖fderiv ℝ g y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ C) ∧
      g =ᶠ[𝓝 a] h := by
  obtain ⟨g, hg, hgc, heq⟩ := exists_compact_C2_extension hh
  obtain ⟨C, hC, hbounds⟩ := compact_C2_derivative_bounds hg hgc
  exact ⟨g, C, hC, hg, hgc, hbounds, heq⟩

end PoincareConjecture
