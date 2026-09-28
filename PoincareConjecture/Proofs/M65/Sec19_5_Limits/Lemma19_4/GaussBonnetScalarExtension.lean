import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetScalarResidual
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

noncomputable section

open Set Filter Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Gauss

private theorem contDiffAt_sum_log_norm (B : Finset ℂ) (m : ℂ → ℕ)
    {x : ℂ} (hx : x ∉ B) :
    ContDiffAt ℝ 1 (fun z : ℂ => ∑ a ∈ B, (m a : ℝ) * Real.log ‖z - a‖) x := by
  apply ContDiffAt.sum
  intro a ha
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr (fun h => hx (h.symm ▸ ha))
  have hsub : ContDiffAt ℝ 1 (fun z : ℂ => z - a) x := contDiffAt_id.sub contDiffAt_const
  exact contDiffAt_const.mul
    ((hsub.norm ℝ hxa).log (norm_ne_zero_iff.mpr hxa))

theorem exists_scalar_residual_extension (B : Finset ℂ) (m : ℂ → ℕ)
    (lambda : ℂ → ℝ) (rho : ℂ → ℂ → ℝ) {U : Set ℂ} (hU : IsOpen U)
    (hlambda : ContDiffOn ℝ 1 lambda U)
    (hpos : ∀ z ∈ U, z ∉ B → 0 < lambda z)
    (hbranch : ∀ a ∈ B, a ∈ U → ContDiffAt ℝ 1 (rho a) a ∧ 0 < rho a a ∧
      ∀ᶠ z in 𝓝 a, lambda z = ‖z - a‖ ^ (2 * m a) * rho a z) :
    ∃ u : ℂ → ℝ, ContDiffOn ℝ 1 u U ∧
      (∀ z ∈ U, z ∉ B →
        u z = Real.log (lambda z) / 2 - ∑ a ∈ B, (m a : ℝ) * Real.log ‖z - a‖) ∧
      ∀ a ∈ B, a ∈ U →
        u a = Real.log (rho a a) / 2 -
          ∑ b ∈ B.erase a, (m b : ℝ) * Real.log ‖a - b‖ := by
  classical
  let base := fun z => Real.log (lambda z) / 2 -
    ∑ a ∈ B, (m a : ℝ) * Real.log ‖z - a‖
  let u := fun z => if z ∈ B then Real.log (rho z z) / 2 -
    ∑ a ∈ B.erase z, (m a : ℝ) * Real.log ‖z - a‖ else base z
  refine ⟨u, ?_, ?_, ?_⟩
  · intro x hxU
    apply ContDiffAt.contDiffWithinAt
    by_cases hxB : x ∈ B
    · obtain ⟨hrho, hpositive, hfactor⟩ := hbranch x hxB hxU
      let germ := fun z => Real.log (rho x z) / 2 -
        ∑ a ∈ B.erase x, (m a : ℝ) * Real.log ‖z - a‖
      have hlocal : ContDiffAt ℝ 1 germ x :=
        ((hrho.log hpositive.ne').div_const 2).sub
          (contDiffAt_sum_log_norm (B.erase x) m (by simp))
      apply hlocal.congr_of_eventuallyEq
      have hnear : ∀ᶠ z in 𝓝 x, z ∉ B.erase x :=
        (B.erase x).finite_toSet.isClosed.compl_mem_nhds (by simp)
      have hposrho : ∀ᶠ z in 𝓝 x, 0 < rho x z :=
        hrho.continuousAt.eventually (lt_mem_nhds hpositive)
      filter_upwards [hnear, hfactor, hposrho] with z hz hf hp
      by_cases hzx : z = x
      · subst z
        simp only [u, if_pos hxB, germ]
      · have hzB : z ∉ B := fun h => hz (Finset.mem_erase.mpr ⟨hzx, h⟩)
        have hs : (∑ a ∈ B, (m a : ℝ) * Real.log ‖z - a‖) =
            (∑ a ∈ B.erase x, (m a : ℝ) * Real.log ‖z - a‖) +
              (m x : ℝ) * Real.log ‖z - x‖ :=
          (Finset.sum_erase_add B (fun a => (m a : ℝ) * Real.log ‖z - a‖) hxB).symm
        have hn : ‖z - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzx)
        dsimp only [u]
        rw [if_neg hzB]
        dsimp only [base, germ]
        rw [hf, hs, Real.log_mul (pow_ne_zero _ hn) hp.ne', Real.log_pow]
        push_cast
        ring
    · have hbase : ContDiffAt ℝ 1 base x :=
        ((((hlambda.contDiffAt (hU.mem_nhds hxU)).log (hpos x hxU hxB).ne').div_const 2).sub
          (contDiffAt_sum_log_norm B m hxB))
      apply hbase.congr_of_eventuallyEq
      filter_upwards [B.finite_toSet.isClosed.compl_mem_nhds hxB] with z hz
      exact if_neg hz
  · intro z _ hz
    exact if_neg hz
  · intro a ha _
    exact if_pos ha

end PoincareConjecture.M65Gauss
