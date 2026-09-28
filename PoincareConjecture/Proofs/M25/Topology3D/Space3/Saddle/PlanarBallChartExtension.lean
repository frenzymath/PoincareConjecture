import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartGermNormalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmallGermExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmallPerturbation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallShrinking
import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology NNReal

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_planar_ball_chart_extension
    (B : BallNeighborhoodChart E2 E2) :
    ∃ G : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
      EqOn G B.chart (closedBall (0 : E2) 1) ∧
      EqOn G.symm B.chart.symm B.closedRegion ∧
      G '' ball (0 : E2) 1 = B.inside ∧
      G '' closedBall (0 : E2) 1 = B.closedRegion ∧
      G '' sphere (0 : E2) 1 = B.boundary := by
  classical
  have hzero : (0 : E2) ∈ B.chart.source := B.closedBall_subset_source (by simp)
  obtain ⟨A, _, h, hh, hh0, hd0, hnormal⟩ :=
    exists_normalized_chart_correction B.chart B.smooth B.smooth_symm hzero
  obtain ⟨g, hg, _, _, hlip, hgerm⟩ :=
    exists_small_germ_extension h hh hh0 hd0
      (L := (1 / 2 : ℝ≥0)) (by norm_num) (b := 1) (by norm_num)
  let F := smallPerturbationDiffeomorph g hg (by norm_num : (1 / 2 : ℝ≥0) < 1) hlip
  let V : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ := {
    toFun := fun y => B.chart 0 + y
    invFun := fun y => y - B.chart 0
    left_inv := fun y => by dsimp; abel
    right_inv := fun y => by dsimp; abel
    contMDiff_toFun := (contDiff_const.add contDiff_id).contMDiff
    contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  let G0 := (A.toDiffeomorph.trans F).trans V
  have hG0 (x : E2) : G0 x = B.chart 0 + A x + g (A x) := by
    change B.chart 0 + (A x + g (A x)) = _
    abel
  have hA0 : Tendsto A (𝓝 (0 : E2)) (𝓝 (0 : E2)) := by
    simpa only [map_zero] using A.continuous.continuousAt.tendsto (x := (0 : E2))
  have hnear : ∀ᶠ x : E2 in 𝓝 0, G0 x = B.chart x := by
    filter_upwards [hA0.eventually hnormal, hA0.eventually hgerm] with x hx hgx
    rw [A.symm_apply_apply] at hx
    rw [hG0, hgx, hx]
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let s : ℝ := min (eps / 2) (1 / 2)
  have hs : 0 < s := lt_min (half_pos heps) (by norm_num)
  have hs1 : s < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hseps : s < eps := (min_le_left _ _).trans_lt (half_lt_self heps)
  let R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ := {
    toFun := fun x => s • x
    invFun := fun x => s⁻¹ • x
    left_inv := fun x => by simp only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    right_inv := fun x => by simp only [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    contMDiff_toFun := (contDiff_const.smul contDiff_id).contMDiff
    contMDiff_invFun := (contDiff_const.smul contDiff_id).contMDiff }
  have hsmall (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      G0 (s • x) = B.chart (s • x) := by
    apply hball
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hs.le).trans_lt
      (by simpa only [mul_one] using hseps)
  obtain ⟨Phi, _, _, htrack, _⟩ := exists_ball_shrinking_isotopy B
  let t : ℝ := -Real.log s
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos hs.le hs1.le)
  have hexp : Real.exp (-t) = s := by
    simpa only [t, neg_neg] using Real.exp_log hs
  let G := (R.trans G0).trans (Phi t).symm
  have hagree : EqOn G B.chart (closedBall (0 : E2) 1) := by
    intro x hx
    change (Phi t).symm (G0 (s • x)) = B.chart x
    rw [hsmall x hx, ← hexp, ← htrack x hx t ht]
    exact (Phi t).symm_apply_apply _
  refine ⟨G, hagree, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    have hgx : G.symm (B.chart x) = x := by
      rw [← hagree hx, G.symm_apply_apply]
    exact hgx.trans (B.chart.left_inv (B.closedBall_subset_source hx)).symm
  · exact image_congr (fun _ hx => hagree (ball_subset_closedBall hx))
  · exact image_congr hagree
  · exact image_congr (fun _ hx => hagree (sphere_subset_closedBall hx))

end PoincareConjecture.M25.Topology3D
