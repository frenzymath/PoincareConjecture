import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryAveragedCutoff
import Mathlib.Analysis.Calculus.Deriv.Slope












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture





theorem m64MonotonePhase_cutoff_flux_sq
    (b q : ℝ → ℝ) (hb : Monotone b) (hq : ContDiff ℝ 1 q)
    {x d T : ℝ} (hx : 0 < x) (hT : x < T) (hd : 0 < d)
    (hq0 : q 0 = 0) (hqT : q T = 0)
    (hqle : ∀ t, q t ≤ 1)
    (hflat : ∀ t ∈ Icc (x - d) (x + d), q t = 1)
    (hleft : MonotoneOn q (Iic x)) (hright : AntitoneOn q (Ici x)) :
    (b (x + d) - b (x - d)) ^ 2 ≤ (∫ t in Icc (0 : ℝ) T, deriv q t * b t) ^ 2 := by
  have hdc : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have hI (a c : ℝ) : IntervalIntegrable (fun t => deriv q t * b t) volume a c :=
    hb.intervalIntegrable.continuousOn_mul hdc.continuousOn
  have hFTC (a c : ℝ) : (∫ t in a..c, deriv q t) = q c - q a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hq.differentiable (by simp) t).hasDerivAt) (hdc.intervalIntegrable a c)
  have hflatd (t : ℝ) (ht : t ∈ Icc (x - d) (x + d)) : deriv q t = 0 := by
    apply IsLocalMax.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun s => by rw [hflat t ht]; exact hqle s)
  have hl (t : ℝ) (ht : t < x) : 0 ≤ deriv q t := by
    rw [← derivWithin_of_mem_nhds (Iic_mem_nhds ht)]
    exact hleft.derivWithin_nonneg
  have hr (t : ℝ) (ht : x < t) : deriv q t ≤ 0 := by
    rw [← derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
    exact hright.derivWithin_nonpos
  have hqcenter : q x = 1 := hflat x ⟨by linarith, by linarith⟩
  have hL : (∫ t in (0 : ℝ)..x, deriv q t * b t) ≤ b (x - d) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..x, deriv q t * b (x - d) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hx.le (hI 0 x)
          ((hdc.intervalIntegrable 0 x).mul_const _)
        intro t ht
        by_cases htt : t ≤ x - d
        · exact mul_le_mul_of_nonneg_left (hb htt) (hl t ht.2)
        · rw [hflatd t ⟨by linarith, by linarith [ht.2]⟩]
          simp
      _ = _ := by rw [intervalIntegral.integral_mul_const, hFTC, hqcenter, hq0]; ring
  have hR : (∫ t in x..T, deriv q t * b t) ≤ -b (x + d) := by
    calc
      _ ≤ ∫ t in x..T, deriv q t * b (x + d) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hT.le (hI x T)
          ((hdc.intervalIntegrable x T).mul_const _)
        intro t ht
        by_cases htt : x + d ≤ t
        · exact mul_le_mul_of_nonpos_left (hb htt) (hr t ht.1)
        · rw [hflatd t ⟨by linarith [ht.1], by linarith⟩]
          simp
      _ = _ := by rw [intervalIntegral.integral_mul_const, hFTC, hqcenter, hqT]; ring
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hI 0 x) (hI x T)
  have hn : 0 ≤ b (x + d) - b (x - d) := sub_nonneg.mpr (hb (by linarith))
  have hflux : b (x + d) - b (x - d) ≤ -(∫ t in (0 : ℝ)..T, deriv q t * b t) := by
    linarith
  have hsq := (sq_le_sq₀ hn (hn.trans hflux)).mpr hflux
  simpa only [neg_sq, intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ T),
    ← integral_Icc_eq_integral_Ioc] using hsq

end PoincareConjecture
