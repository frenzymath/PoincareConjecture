import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ClosingBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.TransportedCap
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_common_enlarged_curved_closing_disk
    {ι : Type*} [Finite ι] {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {b w η : Real} (hw : 0 < w) (hη : 0 < η)
    (a s : ι → Real) (ha : ∀ i, a i < b) (hs : ∀ i, s i < 0)
    (N : ι → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN : ∀ i, EqOn (N i) Q {y | b - η ≤ inner Real v y})
    (E : ι → Set E3)
    (hE : ∀ i, N i '' E i =
      liftPlaneDiffeomorph hv (a i) (s i) (hs i).ne A '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) (a i) b)
    (B : ι → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : ∀ i, B i '' sphere (0 : E3) 1 = E i ∪
      Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v)) :
    ∃ (g : E2 → E3) (r : Real),
      ContDiff Real ∞ g ∧ Injective g ∧ (∀ x, Injective (fderiv Real g x)) ∧
      1 < r ∧
      g '' closedBall (0 : E2) 1 =
        Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v) ∧
      g '' ball (0 : E2) 1 =
        (Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v)) \
          {y | inner Real v y = b} ∧
      (∀ i, g '' closedBall (0 : E2) r ⊆ B i '' sphere (0 : E3) 1) := by
  classical
  obtain ⟨k, hk, hki, hkd, hkb, hkh, hkc, _, hkrange⟩ :=
    exists_cylindrical_cap_over_disk_with_range hv b w hw.ne' A
  let J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro hz; simp [hz] at hv)).repr.symm
  let f : E2 → E3 := k ∘ J
  have hf : ContDiff Real ∞ f := hk.comp J.toContinuousLinearEquiv.contDiff
  have hfi : Injective f := hki.comp J.injective
  have hfd (x : E2) : Injective (fderiv Real f x) := by
    change Injective (fderiv Real (k ∘ J.toContinuousLinearEquiv) x)
    rw [fderiv_comp x
      (hk.differentiable (by simp) _) (J.toContinuousLinearEquiv.differentiable x),
      J.toContinuousLinearEquiv.fderiv]
    exact (hkd (J x)).comp J.injective
  have hfclosed : f '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v := by
    rw [show f = k ∘ J from rfl, image_comp, J.image_closedBall, map_zero]
    exact hkrange
  have hfb (x : E2) (hx : ‖x‖ = 1) : f x = b • v + (A (J x) : E3) :=
    hkb (J x) (by simpa only [J.norm_map] using hx)
  have hfheight (x : E2) (hx : x ∈ closedBall (0 : E2) 1) : b ≤ inner Real v (f x) := by
    have hm := hfclosed ▸ mem_image_of_mem f hx
    obtain ⟨z, hz, heq⟩ := hm
    rw [← heq, inner_liftPlaneDiffeomorph]
    exact le_add_of_nonneg_right (mul_nonneg hw.le
      (height_nonneg_of_mem_boundedCylinderNorthernCap hz))
  have hQinv (y : E3) : inner Real v (Q.symm y) = inner Real v y := by
    rw [← hQ (Q.symm y), Q.apply_symm_apply]
  let V : Set E2 := ball 0 (5 / 4) ∩
    {x | b - η < inner Real v (f x)} ∩ ⋂ i, {x | a i < inner Real v (f x)}
  have hheightcont : Continuous (fun x => inner Real v (f x)) :=
    continuous_const.inner hf.continuous
  have hV : IsOpen V :=
    (isOpen_ball.inter (isOpen_lt continuous_const hheightcont)).inter
      (isOpen_iInter_of_finite (fun _ => isOpen_lt continuous_const hheightcont))
  have hunit : closedBall (0 : E2) 1 ⊆ V := by
    intro x hx
    refine ⟨⟨mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx)
      (by norm_num)), ?_⟩, mem_iInter.mpr (fun i => (ha i).trans_le (hfheight x hx))⟩
    exact (sub_lt_self b hη).trans_le (hfheight x hx)
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_closedBall (0 : E2) 1).exists_cthickening_subset_open hV hunit
  rw [cthickening_closedBall hδ.le (by norm_num : (0 : Real) ≤ 1)] at hδV
  let g : E2 → E3 := Q.symm ∘ f
  have hg : ContDiff Real ∞ g := Q.symm.contDiff.comp hf
  have hgi : Injective g := Q.symm.injective.comp hfi
  have hgclosed : g '' closedBall (0 : E2) 1 =
      Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v) := by
    rw [show g = Q.symm ∘ f from rfl, image_comp, hfclosed]
  refine ⟨g, δ + 1, hg, hgi, ?_, by linarith, hgclosed, ?_, ?_⟩
  · intro x
    rw [show g = Q.symm ∘ f from rfl, fderiv_comp x
      (Q.symm.contDiff.differentiable (by simp) _) (hf.differentiable (by simp) x)]
    have hd := (Q.symm.mfderivToContinuousLinearEquiv (by simp) (f x)).injective
    change Injective (mfderiv (𝓡 3) (𝓡 3) Q.symm (f x)) at hd
    simp only [mfderiv_eq_fderiv, TangentSpace] at hd
    exact hd.comp (hfd x)
  · rw [← hgclosed]
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨mem_image_of_mem g (ball_subset_closedBall hx), ?_⟩
      have hh := hkh (J x) (by simpa only [J.norm_map] using mem_ball_zero_iff.mp hx)
      intro heq
      change inner Real v (Q.symm (f x)) = b at heq
      rw [hQinv] at heq
      change 0 < (inner Real v (f x) - b) / w at hh
      rw [heq, sub_self, zero_div] at hh
      exact lt_irrefl _ hh
    · rintro y ⟨⟨x, hx, rfl⟩, hh⟩
      refine ⟨x, mem_ball_zero_iff.mpr (lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx) ?_), rfl⟩
      intro hn
      apply hh
      change inner Real v (Q.symm (f x)) = b
      rw [hQinv, hfb x hn]
      exact inner_heightCoordinates hv (b, A (J x))
  · intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    by_cases hx1 : ‖x‖ ≤ 1
    · rw [hB i]
      exact Or.inr (hgclosed ▸ mem_image_of_mem g (mem_closedBall_zero_iff.mpr hx1))
    have hxV := hδV hx
    have hxpos : 0 < ‖x‖ := by linarith
    let q : Hemisphere.Plane v := ‖x‖⁻¹ • J x
    have hq : ‖q‖ = 1 := by
      simp only [q, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos), J.norm_map,
        inv_mul_cancel₀ hxpos.ne']
    have hqx : ‖x‖ • q = J x := by
      simp only [q, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    have hfc : f x = (b + w * ((1 - ‖x‖ ^ 2) / (2 * ‖x‖))) • v + (A q : E3) := by
      change k (J x) = _
      rw [← hqx]
      exact hkc q hq ‖x‖ (by linarith) (by linarith [mem_ball_zero_iff.mp hxV.1.1])
    have hfh : inner Real v (f x) = b + w * ((1 - ‖x‖ ^ 2) / (2 * ‖x‖)) := by
      rw [hfc]
      exact inner_heightCoordinates hv (_, A q)
    have hhupper : inner Real v (f x) ≤ b := by
      rw [hfh]
      have hnum : 1 - ‖x‖ ^ 2 ≤ 0 := by nlinarith
      exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hw.le
        (div_nonpos_of_nonpos_of_nonneg hnum (by positivity)))
    have hm : f x ∈ N i '' E i := by
      rw [hE i]
      apply Or.inr
      rw [terminalCylinder_eq_height_product]
      refine ⟨(inner Real v (f x), A q),
        ⟨⟨(mem_iInter.mp hxV.2 i).le, hhupper⟩,
          mem_image_of_mem A (mem_sphere_zero_iff_norm.mpr hq)⟩, ?_⟩
      rw [hfh, hfc]
    have hn : N i (g x) = f x := by
      change N i (Q.symm (f x)) = f x
      have hmem : Q.symm (f x) ∈ {y | b - η ≤ inner Real v y} := by
        change b - η ≤ inner Real v (Q.symm (f x))
        rw [hQinv]
        exact hxV.1.2.le
      rw [hN i hmem, Q.apply_symm_apply]
    obtain ⟨z, hz, heq⟩ := hm
    rw [hB i]
    exact Or.inl ((N i).injective (heq.trans hn.symm) ▸ hz)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
