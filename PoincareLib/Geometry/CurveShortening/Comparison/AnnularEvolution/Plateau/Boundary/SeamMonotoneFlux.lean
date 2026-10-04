import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.MonotoneFlux

/-!
# Monotone phase flux at the affine periodic seam

A test which is one near the two endpoints and zero in the middle
detects the real phase jump across the angular cut. The affine period is
retained explicitly in the flux defect.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareMT

/-- The actual affine seam defect controls the squared two-sided gap of a monotone real
phase. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64MonotonePhase_seam_cutoff_flux_sq
    (b q : ℝ → ℝ) (hb : Monotone b) (hq : ContDiff ℝ 1 q)
    {x d T D : ℝ} (hx : 0 < x) (hT : x < T) (hd : 0 < d)
    (hq0 : q 0 = 1) (hqT : q T = 1) (hqx : q x = 0)
    (hqle : ∀ t, q t ≤ 1)
    (hflat0 : ∀ t ∈ Icc (0 : ℝ) d, q t = 1)
    (hflatT : ∀ t ∈ Icc (T - d) T, q t = 1)
    (hleft : AntitoneOn q (Icc (0 : ℝ) x)) (hright : MonotoneOn q (Icc x T))
    (hperiod : b (T - d) = b (-d) + D) :
    (b d - b (-d)) ^ 2 ≤
      (D - ∫ t in Icc (0 : ℝ) T, deriv q t * b t) ^ 2 := by
  have hdc : Continuous (deriv q) := hq.continuous_deriv (by simp)
  have hI (a c : ℝ) : IntervalIntegrable (fun t => deriv q t * b t) volume a c :=
    hb.intervalIntegrable.continuousOn_mul hdc.continuousOn
  have hFTC (a c : ℝ) : (∫ t in a..c, deriv q t) = q c - q a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hq.differentiable (by simp) t).hasDerivAt) (hdc.intervalIntegrable a c)
  have hflatd (t : ℝ) (ht : q t = 1) : deriv q t = 0 := by
    apply IsLocalMax.deriv_eq_zero
    exact Filter.Eventually.of_forall (fun s => by rw [ht]; exact hqle s)
  have hl (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) x) : deriv q t ≤ 0 := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact hleft.derivWithin_nonpos
  have hr (t : ℝ) (ht : t ∈ Ioo x T) : 0 ≤ deriv q t := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact hright.derivWithin_nonneg
  have hL : (∫ t in (0 : ℝ)..x, deriv q t * b t) ≤ -b d := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..x, deriv q t * b d := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hx.le (hI 0 x)
          ((hdc.intervalIntegrable 0 x).mul_const _)
        intro t ht
        by_cases htt : d ≤ t
        · exact mul_le_mul_of_nonpos_left (hb htt) (hl t ht)
        · rw [hflatd t (hflat0 t ⟨ht.1.le, by linarith⟩)]
          simp
      _ = _ := by rw [intervalIntegral.integral_mul_const, hFTC, hqx, hq0]; ring
  have hR : (∫ t in x..T, deriv q t * b t) ≤ b (T - d) := by
    calc
      _ ≤ ∫ t in x..T, deriv q t * b (T - d) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hT.le (hI x T)
          ((hdc.intervalIntegrable x T).mul_const _)
        intro t ht
        by_cases htt : t ≤ T - d
        · exact mul_le_mul_of_nonneg_left (hb htt) (hr t ht)
        · rw [hflatd t (hflatT t ⟨by linarith, ht.2.le⟩)]
          simp
      _ = _ := by rw [intervalIntegral.integral_mul_const, hFTC, hqx, hqT]; ring
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hI 0 x) (hI x T)
  have hn : 0 ≤ b d - b (-d) := sub_nonneg.mpr (hb (by linarith))
  have hflux : b d - b (-d) ≤ D - (∫ t in (0 : ℝ)..T, deriv q t * b t) := by
    rw [hperiod] at hR
    linarith
  have hsq := (sq_le_sq₀ hn (hn.trans hflux)).mpr hflux
  simpa only [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ T),
    ← integral_Icc_eq_integral_Ioc] using hsq

end PoincareMT
