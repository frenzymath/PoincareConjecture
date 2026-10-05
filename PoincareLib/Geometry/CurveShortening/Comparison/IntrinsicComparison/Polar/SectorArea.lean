import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Corner.TangentCones
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact area of an actual polar sector

The polar Jacobian computes the area directly. This is the quantitative
step needed to convert the proved tangent-sector area partition into
the sum of the metric corner angles.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ENNReal Topology

namespace PoincareMT

private theorem radial_lintegral {R : ℝ} (hR : 0 < R) :
    (∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal r) = ENNReal.ofReal (R ^ 2 / 2) := by
  have hint : IntegrableOn (fun r : ℝ => r) (Ioo 0 R) :=
    (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hpos : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) R)] (fun r : ℝ => r) :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun _ hr => hr.1.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hpos,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_id]
  norm_num

/-- The open polar sector has its exact Euclidean area, obtained from the polar Jacobian and
the radial integral. The angular interval may touch either endpoint of the polar chart.
Source: Morgan--Tian Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471; the explicit project tangent-fan derivation is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_polar_sector_volume
    {R a d : ℝ} (hR : 0 < R) (ha : -Real.pi ≤ a) (hd : d ≤ Real.pi) :
    volume (polarCoord.symm '' (Ioo (0 : ℝ) R ×ˢ Ioo a d)) =
      ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal (d - a) := by
  have hbox : Ioo (0 : ℝ) R ×ˢ Ioo a d ⊆ polarCoord.target := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    exact ⟨hr.1, ha.trans_lt ht.1, ht.2.trans_le hd⟩
  have hjac := lintegral_abs_det_fderiv_eq_addHaar_image volume
    (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun p (_ : p ∈ Ioo (0 : ℝ) R ×ˢ Ioo a d) =>
      (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    (polarCoord.symm.injOn.mono hbox)
  rw [← hjac]
  have hradial : (∫⁻ p in Ioo (0 : ℝ) R ×ˢ Ioo a d,
      ENNReal.ofReal |(fderivPolarCoordSymm p).det|) =
      ∫⁻ p in Ioo (0 : ℝ) R ×ˢ Ioo a d, ENNReal.ofReal p.1 := by
    apply setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    change ENNReal.ofReal |(fderivPolarCoordSymm p).det| = ENNReal.ofReal p.1
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1.1]
  rw [hradial]
  change (∫⁻ p in Ioo (0 : ℝ) R ×ˢ Ioo a d, ENNReal.ofReal p.1
    ∂(volume.prod volume)) = _
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [lintegral_mul_const _ (show Measurable (fun r : ℝ => ENNReal.ofReal r) by fun_prop),
    radial_lintegral hR]

end PoincareMT
