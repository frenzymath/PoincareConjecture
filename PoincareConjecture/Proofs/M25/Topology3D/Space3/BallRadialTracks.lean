import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartRadialField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowAlgebra










set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem exists_ball_radial_field [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (B : BallNeighborhoodChart E F) :
    ∃ W : F → F, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      tsupport W ⊆ B.chart.target ∧ EqOn W (chartRadialField B.chart) B.closedRegion := by
  have hsub : B.closedRegion ⊆ B.chart.target := by
    rintro y ⟨x, hx, rfl⟩
    exact B.chart.map_source (B.closedBall_subset_source hx)
  obtain ⟨W, hW, hWc, hWs, hag⟩ := exists_compactField_extension
    B.closedRegion_compact B.chart.open_target hsub (chartRadialField B.chart)
    (chartRadialField_contDiffOn B.chart B.smooth B.smooth_symm)
  refine ⟨W, hW, hWc, hWs, ?_⟩
  intro y hy
  exact (eventually_nhdsSet_iff_forall.mp hag y hy).self_of_nhds



theorem boundedFlow_eq_chart_radial [CompleteSpace F] (B : BallNeighborhoodChart E F)
    (W : F → F) {K L : ℝ≥0} (hK : LipschitzWith K W) (hL : ∀ y, ‖W y‖ ≤ L)
    (hag : EqOn W (chartRadialField B.chart) B.closedRegion)
    {x : E} (hx : x ∈ closedBall 0 1) {t : ℝ} (ht : 0 ≤ t) :
    boundedFlow W hK hL (B.chart x) t = B.chart (Real.exp (-t) • x) := by
  have hscale (s : ℝ) (hs : 0 ≤ s) : Real.exp (-s) • x ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx)
      (Real.exp_pos _).le).trans (by simpa only [mul_one] using hexp)
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt
      (fun u => B.chart (Real.exp (-u) • x))
      (W (B.chart (Real.exp (-s) • x))) s := by
    rw [hag ⟨Real.exp (-s) • x, hscale s hs, rfl⟩]
    exact chartRadialField_track_hasDerivAt B.chart B.smooth x s
      (B.closedBall_subset_source (hscale s hs))
  have heq : EqOn (boundedFlow W hK hL (B.chart x))
      (fun s => B.chart (Real.exp (-s) • x)) (Icc 0 t) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ y => W y) (s := fun _ => univ) (fun _ _ => hK.lipschitzOnWith)
    · exact fun s _ =>
        (boundedFlow_hasDerivAt W hK hL (B.chart x) s).continuousAt.continuousWithinAt
    · exact fun s _ => (boundedFlow_hasDerivAt W hK hL (B.chart x) s).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · exact fun s hs => (hd s hs.1).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s hs.1).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
    · simp only [boundedFlow_zero, neg_zero, Real.exp_zero, one_smul]
  exact heq ⟨ht, le_rfl⟩

end PoincareConjecture.M25.Topology3D
