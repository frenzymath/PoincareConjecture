import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Height
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Topology Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]

omit [FiniteDimensional Real E] in
theorem contDiffAt_boundedCapHeight_norm_sq {x : E} (hx : ‖x‖ < 1) :
    ContDiffAt Real ∞ (fun y : E => boundedCapHeight (‖y‖ ^ 2)) x := by
  have hsq : ContDiff Real ∞ (fun y : E => ‖y‖ ^ 2) := by
    simpa only [id_eq, real_inner_self_eq_norm_sq] using
      (contDiff_id.inner Real contDiff_id :
        ContDiff Real ∞ (fun y : E => inner Real y y))
  exact (contDiffAt_boundedCapHeight (by nlinarith [norm_nonneg x])).comp x hsq.contDiffAt

theorem exists_smooth_cap_height_difference
    (P : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞)
    (hball : P '' ball (0 : E) 1 = ball (0 : E) 1)
    {ε : Real} (hε : 0 < ε) (_hε1 : ε < 1)
    (hcollar : ∀ x : E, |‖x‖ - 1| < ε → ‖P x‖ = ‖x‖) :
    ∃ b : E → Real, ContDiff Real ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ ball (0 : E) 1 ∧
      (∀ x ∈ ball (0 : E) 1, b x =
        boundedCapHeight (‖x‖ ^ 2) - boundedCapHeight (‖P.symm x‖ ^ 2)) ∧
      (∀ x ∉ ball (0 : E) 1, b x = 0) := by
  classical
  let b : E → Real := fun x => if x ∈ ball (0 : E) 1 then
    boundedCapHeight (‖x‖ ^ 2) - boundedCapHeight (‖P.symm x‖ ^ 2) else 0
  let K : Set E := P '' closedBall (0 : E) (1 - ε / 2)
  have hK : IsCompact K := (isCompact_closedBall _ _).image P.continuous
  have hinside (x : E) (hx : x ∈ ball (0 : E) 1) : P.symm x ∈ ball (0 : E) 1 := by
    rw [← hball] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hKB : K ⊆ ball (0 : E) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hball]
    refine ⟨x, ?_, rfl⟩
    rw [mem_ball_zero_iff]
    rw [mem_closedBall_zero_iff] at hx
    linarith
  have hbzero (x : E) (hx : x ∉ K) : b x = 0 := by
    by_cases hxb : x ∈ ball (0 : E) 1
    · have hp : ‖P.symm x‖ < 1 := mem_ball_zero_iff.mp (hinside x hxb)
      have hpout : 1 - ε / 2 < ‖P.symm x‖ := by
        apply lt_of_not_ge
        intro h
        exact hx ⟨P.symm x, mem_closedBall_zero_iff.mpr h, P.apply_symm_apply x⟩
      have hpc : |‖P.symm x‖ - 1| < ε := abs_lt.mpr ⟨by linarith, by linarith⟩
      have heq : ‖x‖ = ‖P.symm x‖ := by simpa using hcollar (P.symm x) hpc
      simp only [b, if_pos hxb, heq, sub_self]
    · exact if_neg hxb
  have hbsupport : tsupport b ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hnot
    exact hx (hbzero x hnot)
  have hb : ContDiff Real ∞ b := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball (0 : E) 1
    · have h1 := contDiffAt_boundedCapHeight_norm_sq (mem_ball_zero_iff.mp hx)
      have h2 := (contDiffAt_boundedCapHeight_norm_sq
        (mem_ball_zero_iff.mp (hinside x hx))).comp x P.symm.contMDiff.contDiff.contDiffAt
      apply (h1.sub h2).congr_of_eventuallyEq
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact if_pos hy
    · have hxK : x ∉ K := fun h => hx (hKB h)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hbzero y hy
  exact ⟨b, hb, hK.of_isClosed_subset isClosed_closure hbsupport,
    hbsupport.trans hKB, fun x hx => if_pos hx, fun x hx => if_neg hx⟩

end Poincare.Manifold.Schoenflies
