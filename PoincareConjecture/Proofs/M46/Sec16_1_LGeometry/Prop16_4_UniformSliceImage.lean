import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyRestart
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.Proofs.M46

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem surjOn_closedBall_of_derivative_close_identity
    {f : E → E} {D : E → E →L[ℝ] E} {x₀ : E} {R : ℝ} (hR : 0 ≤ R)
    (hder : ∀ z ∈ closedBall x₀ R, HasFDerivAt f (D z) z)
    (hbound : ∀ z ∈ closedBall x₀ R, ‖D z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    SurjOn f (closedBall x₀ R) (closedBall (f x₀) (R / 2)) := by
  have happrox : ApproximatesLinearOn f (ContinuousLinearMap.id ℝ E)
      (closedBall x₀ R) (1 / 2 : ℝ≥0) := by
    intro x hx y hy
    have hd (z : E) (hz : z ∈ closedBall x₀ R) :
        HasFDerivWithinAt (fun w => f w - w)
          (D z - ContinuousLinearMap.id ℝ E) (closedBall x₀ R) z :=
      ((hder z hz).sub (hasFDerivAt_id z)).hasFDerivWithinAt
    have hh := (convex_closedBall x₀ R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hd hbound hy hx
    have heq : (f x - x) - (f y - y) = f x - f y - (x - y) := by abel
    simpa only [heq, ContinuousLinearMap.id_apply, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat] using hh
  let inv : (ContinuousLinearMap.id ℝ E).NonlinearRightInverse := {
    toFun := id
    nnnorm := 1
    bound' := by intro y; simp
    right_inv' := by intro y; rfl
  }
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse inv hR Subset.rfl
  have hradius : ((inv.nnnorm : ℝ)⁻¹ - (1 / 2 : ℝ≥0)) * R = R / 2 := by
    change ((1 : ℝ)⁻¹ - ((1 / 2 : ℝ≥0) : ℝ)) * R = R / 2
    norm_num
    ring
  rwa [hradius] at hsurj

theorem closedFamily_exists_uniform_image_ball {C : Set ℝ} {U : Set E}
    (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (alpha : E × ℝ → E)
    (halpha : ContDiffOn ℝ ∞ alpha (U ×ˢ C)) {x₀ : E} (hx₀ : x₀ ∈ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ C) (hinit : ∀ x ∈ U, alpha (x, t₀) = x) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ t in 𝓝[C] t₀,
      SurjOn (fun x => alpha (x, t)) U (ball x₀ r) := by
  let f : ℝ × E → E := fun z => alpha (z.2, z.1)
  have hf : ContDiffOn ℝ ∞ f (C ×ˢ U) :=
    halpha.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hz => ⟨hz.2, hz.1⟩)
  let D := M08.spatialWithinFDeriv C U f
  have hd (t : ℝ) (ht : t ∈ C) (x : E) (hx : x ∈ U) :
      HasFDerivAt (fun y => alpha (y, t)) (D (t, x)) x :=
    M08.hasFDerivAt_spatialWithin hU f hf ht hx
  have hD₀ : D (t₀, x₀) = ContinuousLinearMap.id ℝ E := by
    have heq : (fun y => alpha (y, t₀)) =ᶠ[𝓝 x₀] id := by
      filter_upwards [hU.mem_nhds hx₀] with y hy
      exact hinit y hy
    have hh := (hd t₀ ht₀ x₀ hx₀).fderiv
    rw [heq.fderiv_eq, fderiv_id] at hh
    exact hh.symm
  have hc := (M08.spatialWithinFDeriv_contDiffOn hC hU f hf).continuousOn
  have hnear : {z : ℝ × E | ‖D z - ContinuousLinearMap.id ℝ E‖ < 1 / 2} ∈
      𝓝[C ×ˢ U] (t₀, x₀) := by
    have hzero : ‖D (t₀, x₀) - ContinuousLinearMap.id ℝ E‖ < 1 / 2 := by
      rw [hD₀, sub_self, norm_zero]
      norm_num
    exact (((hc (t₀, x₀) ⟨ht₀, hx₀⟩).sub continuousWithinAt_const).norm).eventually
      (gt_mem_nhds hzero)
  rw [nhdsWithin_prod_eq, nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx₀)] at hnear
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.mp hnear
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hB (hU.mem_nhds hx₀))
  let rho := R / 2
  have hrho : 0 < rho := half_pos hR
  have hclosed : closedBall x₀ rho ⊆ B ∩ U := by
    intro z hz
    exact hball ((Metric.mem_closedBall.mp hz).trans_lt (by dsimp [rho]; linarith))
  have hcenter : ContinuousWithinAt (fun t => alpha (x₀, t)) C t₀ :=
    (halpha.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨hx₀, ht⟩)) t₀ ht₀
  have hcenterNear : ∀ᶠ t in 𝓝[C] t₀, dist (alpha (x₀, t)) x₀ < rho / 4 := by
    have hh := hcenter.eventually (Metric.ball_mem_nhds (alpha (x₀, t₀)) (by positivity :
      0 < rho / 4))
    simpa only [hinit x₀ hx₀, mem_ball] using hh
  refine ⟨rho / 4, by positivity, ?_⟩
  filter_upwards [hA, hcenterNear, self_mem_nhdsWithin] with t ht hcenterDist htC
  have hsurj := surjOn_closedBall_of_derivative_close_identity hrho.le
    (fun z hz => hd t htC z (hclosed hz).2)
    (fun z hz => (hAB ⟨ht, (hclosed hz).1⟩).le)
  intro y hy
  have hy' : y ∈ closedBall (alpha (x₀, t)) (rho / 2) := by
    apply Metric.mem_closedBall.mpr
    have htriangle := dist_triangle y x₀ (alpha (x₀, t))
    rw [dist_comm x₀] at htriangle
    have hyDist := Metric.mem_ball.mp hy
    linarith
  obtain ⟨z, hz, heq⟩ := hsurj hy'
  exact ⟨z, (hclosed hz).2, heq⟩

end PoincareConjecture.Proofs.M46
