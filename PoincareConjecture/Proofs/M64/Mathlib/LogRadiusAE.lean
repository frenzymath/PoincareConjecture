import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory

namespace PoincareConjecture




theorem m64LogRadius_ae {rho : ℝ} (hrho : 0 < rho) {q : ℝ → Prop}
    (hq : ∀ᵐ r ∂volume.restrict (Icc (rho * Real.exp (-1)) rho), q r) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), q (rho * Real.exp (-s)) := by
  classical
  let f := fun s : ℝ => rho * Real.exp (-s)
  let d := fun s : ℝ => -(rho * Real.exp (-s))
  let F := fun r : ℝ => if q r then (0 : ℝ) else 1
  have hf (s : ℝ) : HasDerivAt f (d s) s := by
    simpa [f, d] using
      (((hasDerivAt_id s).neg.exp).const_mul rho)
  have hinj : InjOn f (Icc (0 : ℝ) 1) := by
    intro s _ t _ h
    exact neg_injective (Real.exp_injective (mul_left_cancel₀ hrho.ne' h))
  have hsub : f '' Icc (0 : ℝ) 1 ⊆ Icc (rho * Real.exp (-1)) rho := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hs.2])) hrho.le,
      mul_le_of_le_one_right hrho.le
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1))⟩
  have hz : F =ᵐ[volume.restrict (f '' Icc (0 : ℝ) 1)] (fun _ => (0 : ℝ)) :=
    (ae_restrict_of_ae_restrict_of_subset hsub hq).mono (fun r hr => by simp [F, hr])
  have hi : IntegrableOn F (f '' Icc (0 : ℝ) 1) := (integrable_zero _ _ _).congr hz.symm
  have hwi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (fun s _ => (hf s).hasDerivWithinAt) hinj F).mp hi
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s _ => (hf s).hasDerivWithinAt) hinj F
  have hzero : (∫ s in Icc (0 : ℝ) 1, |d s| * F (f s)) = 0 := by
    rw [← show (∫ s in Icc (0 : ℝ) 1, |d s| • F (f s)) =
        ∫ s in Icc (0 : ℝ) 1, |d s| * F (f s) from rfl, ← heq]
    simpa only [integral_zero] using integral_congr_ae hz
  have hpos (r : ℝ) : 0 ≤ F r := by dsimp only [F]; split_ifs <;> norm_num
  have hgood := (integral_eq_zero_iff_of_nonneg
    (fun s => mul_nonneg (abs_nonneg _) (hpos _)) hwi).mp hzero
  filter_upwards [hgood] with s hs
  by_contra hnot
  change ¬ q (f s) at hnot
  have hd : 0 < |d s| := abs_pos.mpr (neg_ne_zero.mpr (mul_ne_zero hrho.ne' (Real.exp_ne_zero _)))
  simp only [F, if_neg hnot, mul_one, Pi.zero_apply] at hs
  exact hd.ne' hs

end PoincareConjecture
