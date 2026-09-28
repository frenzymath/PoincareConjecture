import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeCalculus
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem isUnit_clm_injective {P : E →L[ℂ] E} (hP : IsUnit P) :
    Function.Injective P := by
  intro v w h
  have hh := congrArg (fun y => Ring.inverse P y) h
  change (Ring.inverse P * P) v = (Ring.inverse P * P) w at hh
  rw [Ring.inverse_mul_cancel _ hP] at hh
  exact hh

variable [CompleteSpace E]

theorem differentiableOn_inverse_matrix_field
    {A P : ℂ → E →L[ℂ] E} {F : ℂ → E} {s : Set ℂ}
    (hs : IsOpen s) (hP : ContDiff ℝ 1 P) (hunit : ∀ z, IsUnit (P z))
    (hPeq : ∀ z, dbar P z = A z * P z)
    (hF : ContDiffOn ℝ 1 F s) (hFeq : ∀ z ∈ s, dbar F z = A z (F z)) :
    DifferentiableOn ℂ (fun z => Ring.inverse (P z) (F z)) s := by
  let H := fun z => Ring.inverse (P z) (F z)
  let L := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hPH : (fun z => P z (H z)) = F := by
    funext z
    change (P z * Ring.inverse (P z)) (F z) = F z
    rw [Ring.mul_inverse_cancel _ (hunit z)]
    rfl
  intro z hz
  have hInv : ContDiffAt ℝ 1 (fun w => Ring.inverse (P w)) z := by
    obtain ⟨u, hu⟩ := hunit z
    have hi : ContDiffAt ℝ 1 Ring.inverse (P z) := by
      simpa only [hu] using contDiffAt_ringInverse ℝ (n := 1) u
    exact hi.comp z hP.contDiffAt
  have hFz : ContDiffAt ℝ 1 F z := hF.contDiffAt (hs.mem_nhds hz)
  have hH : DifferentiableAt ℝ H z :=
    ((L.contDiff.contDiffAt.comp z hInv).clm_apply hFz).differentiableAt one_ne_zero
  have hp := dbar_clm_apply (hP.differentiable one_ne_zero z) hH
  rw [hPH, hFeq z hz, hPeq z] at hp
  change A z (F z) = A z (P z (H z)) + P z (dbar H z) at hp
  rw [show P z (H z) = F z from congrFun hPH z] at hp
  have hzP : P z (dbar H z) = 0 := by
    apply add_left_cancel (a := A z (F z))
    simpa only [add_zero] using hp.symm
  have hzH : dbar H z = 0 :=
    isUnit_clm_injective (hunit z) (by simpa only [map_zero] using hzP)
  exact (differentiableAt_complex_of_dbar_eq_zero hH hzH).differentiableWithinAt

theorem exists_power_factor_of_matrix_field
    {A P : ℂ → E →L[ℂ] E} {F : ℂ → E} {s : Set ℂ} {z0 : ℂ}
    (hs : IsOpen s) (hz0 : z0 ∈ s) (hP : ContDiff ℝ 1 P)
    (hunit : ∀ z, IsUnit (P z)) (hPeq : ∀ z, dbar P z = A z * P z)
    (hF : ContDiffOn ℝ 1 F s) (hFeq : ∀ z ∈ s, dbar F z = A z (F z))
    (hnot : ¬∀ᶠ z in 𝓝 z0, F z = 0) :
    ∃ (n : ℕ) (G : ℂ → E), ContDiffAt ℝ 1 G z0 ∧ G z0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 z0, F z = (z - z0) ^ n • G z := by
  let H := fun z => Ring.inverse (P z) (F z)
  have hPH (z : ℂ) : P z (H z) = F z := by
    change (P z * Ring.inverse (P z)) (F z) = F z
    rw [Ring.mul_inverse_cancel _ (hunit z)]
    rfl
  have hH : AnalyticAt ℂ H z0 :=
    (differentiableOn_inverse_matrix_field hs hP hunit hPeq hF hFeq).analyticAt
      (hs.mem_nhds hz0)
  have hnotH : ¬∀ᶠ z in 𝓝 z0, H z = 0 := by
    intro hzero
    apply hnot
    filter_upwards [hzero] with z hz
    rw [← hPH z, hz, map_zero]
  obtain ⟨n, g, hg, hg0, hfactor⟩ :=
    hH.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotH
  let G := fun z => P z (g z)
  let L := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hG : ContDiffAt ℝ 1 G z0 :=
    (L.contDiff.contDiffAt.comp z0 hP.contDiffAt).clm_apply
      ((hg.contDiffAt : ContDiffAt ℂ 1 g z0).restrict_scalars ℝ)
  refine ⟨n, G, hG, ?_, ?_⟩
  · intro hzero
    apply hg0
    exact isUnit_clm_injective (hunit z0) (by simpa only [map_zero] using hzero)
  · filter_upwards [hfactor] with z hz
    rw [← hPH z, hz, map_smul]

end PoincareConjecture.M65Branch
