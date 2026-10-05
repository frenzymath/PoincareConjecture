import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Polar.Integration
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating on the actual angular rectangle

The Fubini step in Morgan--Tian Claim 19.23, pp. 453-454. The closed M58
coordinate equivalence preserves Euclidean volume. The angular variable
is integrated first, giving the actual total curvature at each time.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareMT

/-- Euclidean area integration on the frozen annulus rectangle equals
the iterated angular-then-time integral; Claim 19.23, pp. 453-454. -/
theorem m65Integral_annulusDomain {f : LoopPlane → ℝ} (hf : Continuous f) :
    (∫ p in m64AnnulusDomain, f p) =
      ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..curvePeriod, f (annulusPoint x y) := by
  let e := Proofs.M58.loopPlaneEquivProd
  have hset : e.symm ⁻¹' m64AnnulusDomain = Icc 0 curvePeriod ×ˢ Icc (0 : ℝ) 1 := by
    ext p
    change (0 ≤ p.1 ∧ p.1 ≤ curvePeriod ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) ↔
      (0 ≤ p.1 ∧ p.1 ≤ curvePeriod) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)
    tauto
  have hcont : Continuous (fun p : ℝ × ℝ => f (annulusPoint p.2 p.1)) := by
    apply hf.comp
    unfold annulusPoint
    fun_prop
  calc
    _ = ∫ p in Icc 0 curvePeriod ×ˢ Icc (0 : ℝ) 1, f (annulusPoint p.1 p.2) := by
      have h := Proofs.M58.measurePreserving_loopPlaneEquivProd.symm.setIntegral_preimage_emb
        e.symm.measurableEmbedding f m64AnnulusDomain
      rw [hset] at h
      exact h.symm
    _ = ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc 0 curvePeriod, f (annulusPoint p.2 p.1) :=
      (setIntegral_prod_swap _ _ _).symm
    _ = ∫ y in Icc (0 : ℝ) 1, ∫ x in Icc 0 curvePeriod, f (annulusPoint x y) :=
      setIntegral_prod _ (hcont.continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc))
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by unfold curvePeriod; positivity)]

end PoincareMT
