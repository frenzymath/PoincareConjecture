import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Radial
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

namespace Poincare.Riemannian.RadialTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local instance : NormedAddCommGroup (F →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

theorem exists_field_local
    {Γ : E → E →L[ℝ] F →L[ℝ] F} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hΓ : ContDiffOn ℝ ∞ Γ U) (v : F) :
    ∃ (r : ℝ) (Y : E → F), 0 < r ∧ ball 0 r ⊆ U ∧
      ContDiff ℝ ∞ Y ∧ Y 0 = v ∧
      (∀ u ∈ ball 0 r, ∀ t ∈ Icc (-1 : ℝ) 1,
        HasDerivAt (fun s : ℝ => Y (s • u)) (-(Γ (t • u) u (Y (t • u)))) t) ∧
      (∀ u, covariantDerivative Γ Y 0 u = 0) ∧
      (∀ u, covariantDerivative Γ (fun x => covariantDerivative Γ Y x u) 0 u = 0) := by
  obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hzero)
  let χ : ContDiffBump (0 : E) :=
    { rIn := d / 2, rOut := d, rIn_pos := half_pos hd,
      rIn_lt_rOut := half_lt_self hd }
  let Γ' : E → E →L[ℝ] F →L[ℝ] F := fun x => χ x • Γ x
  have hΓ' : ContDiff ℝ ∞ Γ' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (χ : E → ℝ)
    · have hxU : x ∈ U := hdU (by simpa [χ.tsupport_eq] using hx)
      exact χ.contDiff.contDiffAt.smul (hΓ.contDiffAt (hU.mem_nhds hxU))
    · have heq : Γ' =ᶠ[𝓝 x] fun _ => (0 : E →L[ℝ] F →L[ℝ] F) := by
        filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hx]
          with y hy
        exact show χ y • Γ y = 0 by rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hagree : EqOn Γ' Γ (ball 0 (d / 2)) := by
    intro x hx
    exact show χ x • Γ x = Γ x by
      rw [χ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]
  have heq : Γ' =ᶠ[𝓝 0] Γ :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self (half_pos hd))) hagree
  let Y := field Γ' v
  have hY : ContDiff ℝ ∞ Y := contDiff_field hΓ' v
  have hfirst (u : E) : covariantDerivative Γ Y 0 u = 0 := by
    rw [covariantDerivative, ← heq.self_of_nhds]
    exact covariantDerivative_field_zero hΓ' v u
  refine ⟨d / 2, Y, half_pos hd,
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hd.le))).trans hdU,
    hY, field_zero hΓ' v, ?_, hfirst, ?_⟩
  · intro u hu t ht
    have htu : t • u ∈ ball 0 (d / 2) := by
      rw [mem_ball, dist_zero_right] at hu ⊢
      rw [norm_smul, Real.norm_eq_abs]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg u) (abs_le.mpr ht)) hu
    have h := ((hY.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const u)
    have hc := covariantDerivative_field_radial_all hΓ' v u t
    change fderiv ℝ Y (t • u) u + Γ' (t • u) u (Y (t • u)) = 0 at hc
    rw [hagree htu] at hc
    simpa only [Function.comp_def, id_eq, one_smul, eq_neg_of_add_eq_zero_left hc] using h
  · intro u
    have hconn : (fun x => covariantDerivative Γ' Y x u) =ᶠ[𝓝 0]
        (fun x => covariantDerivative Γ Y x u) := by
      filter_upwards [heq] with x hx
      simp only [covariantDerivative, hx]
    have hd := hconn.fderiv_eq (𝕜 := ℝ)
    have hconn0 : covariantDerivative Γ' Y 0 u = covariantDerivative Γ Y 0 u :=
      hconn.self_of_nhds
    have hz := secondCovariantDerivative_field_zero hΓ' v u
    change fderiv ℝ (fun x => covariantDerivative Γ' Y x u) 0 u +
      Γ' 0 u (covariantDerivative Γ' Y 0 u) = 0 at hz
    rw [hd, hconn0, heq.self_of_nhds] at hz
    exact hz

end Poincare.Riemannian.RadialTransport
