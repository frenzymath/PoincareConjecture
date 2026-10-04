import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Relabeling.Differential

/-!
# Curvature energy through fixed labels

The actual spatial energy and the lower length inequality transport with
the original constants and included endpoints. Source: corrected Lemma 0.4
and Corollary 19.10, MT2015Correction pp. 7-8; see
`2026-09-21-c2-estimates-from-local.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) {c d : ℝ → ℝ → M}
  {phi : ℝ → ℝ} {t : ℝ}

/-- The actual spatial curvature energy agrees under the supplied fixed
relabeling at every included time. Correction pp. 7-8. -/
theorem curvatureEnergy_eq_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ y, 0 < deriv phi y)
    (hshift : ∀ y, phi (y + curvePeriod) = phi y + curvePeriod)
    (ht : t ∈ Icc a b) (hcd : ∀ y, c y t = d (phi y) t) :
    (∫ y in (0 : ℝ)..curvePeriod, m62CurvatureSquared F c t y * curveSpeed F c t y) =
      ∫ y in (0 : ℝ)..curvePeriod, m62CurvatureSquared F d t y * curveSpeed F d t y := by
  calc
    _ = ∫ y in (0 : ℝ)..curvePeriod,
        m62CurvatureSquared F (fun z s => d (phi z) s) t y *
          curveSpeed F (fun z s => d (phi z) s) t y := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      rw [curvatureSquared_congr_slice F hcd, curveSpeed_congr_slice F hcd]
    _ = _ := smooth_curvatureEnergy_comp F d hd hphi hpos hshift ht

/-- M62's length inequality retains its actual curvature-energy loss on
the original labels. Every integral is certified integrable before
linearity is used; correction Lemma 0.4 and Corollary 19.10, pp. 7-8. -/
theorem length_energy_bound_of_relabeling (hd : M62ShrinkingCurve F d)
    (hphi : ContDiff ℝ 1 phi) (hpos : ∀ y, 0 < deriv phi y)
    (hshift : ∀ y, phi (y + curvePeriod) = phi y + curvePeriod)
    (hcd : ∀ s ∈ Icc a b, ∀ y, c y s = d (phi y) s)
    {K0 K1 K2 : ℝ} (hE : M62CurveEstimates F d K0 K1 K2) (ht : t ∈ Ioo a b) :
    deriv (m62Length F c) t +
        (∫ y in (0 : ℝ)..curvePeriod, m62CurvatureSquared F c t y * curveSpeed F c t y) ≤
      K2 * m62Length F c t := by
  have ht' := Ioo_subset_Icc_self ht
  have hkcont : Continuous (fun y => m62CurvatureSquared F d t y * curveSpeed F d t y) :=
    ((M62.curvatureSquared_continuousOn F d hd).mul
      (M62.speed_continuousOn F d hd)).comp_continuous
        (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht'⟩)
  have hkint : IntervalIntegrable
      (fun y => m62CurvatureSquared F d t y * curveSpeed F d t y)
      MeasureTheory.volume 0 curvePeriod := hkcont.intervalIntegrable 0 curvePeriod
  have hvint := hE.length_integrable t ht'
  have hidensity : (∫ y in (0 : ℝ)..curvePeriod,
      (K2 - m62CurvatureSquared F d t y) * curveSpeed F d t y) =
      K2 * m62Length F d t -
        ∫ y in (0 : ℝ)..curvePeriod, m62CurvatureSquared F d t y * curveSpeed F d t y := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (hvint.const_mul K2) hkint,
      intervalIntegral.integral_const_mul]
    rfl
  have hbound := hE.length_bound t ht
  rw [hidensity] at hbound
  have heq : m62Length F c =ᶠ[𝓝 t] m62Length F d := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact length_eq_of_relabeling F hd hphi hpos hshift hs (hcd s hs)
  rw [heq.deriv_eq, curvatureEnergy_eq_of_relabeling F hd hphi hpos hshift ht' (hcd t ht'),
    length_eq_of_relabeling F hd hphi hpos hshift ht' (hcd t ht')]
  linarith only [hbound]

end PoincareMT.M63
