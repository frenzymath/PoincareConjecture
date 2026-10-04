import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Infimum
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Domain.Boundary
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Polar.Integration
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Iterated integration on the annular rectangle

The source measure in the M64 definitions is transported to the product
coordinates by M58's volume-preserving equivalence. The null boundary then
identifies the closed-domain energy with the interior energy used by weak
compactness and by the trace estimates.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareMT

open Proofs.M58

private theorem m64AnnulusDomain_ae_eq_interior :
    m64AnnulusDomain =ᵐ[volume] interior m64AnnulusDomain := by
  apply ae_eq_set.mpr
  exact ⟨m64AnnulusDomain_boundary_null, by rw [sdiff_eq_empty.mpr interior_subset]; simp⟩

/-- Transport the actual continuous scalar integral on the closed annulus to product
coordinates. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusIntegral_eq_iterated (F : LoopPlane → ℝ) (hF : Continuous F) :
    (∫ p in m64AnnulusDomain, F p) =
      ∫ x in Icc (0 : ℝ) curvePeriod, ∫ s in Icc (0 : ℝ) 1, F (annulusPoint x s) := by
  let T := Icc (0 : ℝ) curvePeriod ×ˢ Icc (0 : ℝ) 1
  have hT : MeasurableSet T := measurableSet_Icc.prod measurableSet_Icc
  have heq (q : ℝ × ℝ) : loopPlaneEquivProd.symm q = annulusPoint q.1 q.2 := by
    ext i
    fin_cases i <;> rfl
  have hmem (q : ℝ × ℝ) : loopPlaneEquivProd.symm q ∈ m64AnnulusDomain ↔ q ∈ T := by
    rw [heq]
    change (0 ≤ q.1 ∧ q.1 ≤ curvePeriod ∧ 0 ≤ q.2 ∧ q.2 ≤ 1) ↔
      (0 ≤ q.1 ∧ q.1 ≤ curvePeriod) ∧ (0 ≤ q.2 ∧ q.2 ≤ 1)
    tauto
  have hcont : Continuous (fun q : ℝ × ℝ => F (annulusPoint q.1 q.2)) := by
    apply hF.comp
    unfold annulusPoint
    fun_prop
  have hInt : IntegrableOn (fun q : ℝ × ℝ => F (annulusPoint q.1 q.2)) T
      (volume.prod volume) :=
    hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc
    _ = ∫ p, m64AnnulusDomain.indicator F p :=
      (integral_indicator m64AnnulusDomain_measurableSet).symm
    _ = ∫ q : ℝ × ℝ, m64AnnulusDomain.indicator F (loopPlaneEquivProd.symm q) :=
      (measurePreserving_loopPlaneEquivProd.symm.integral_comp' _).symm
    _ = ∫ q in T, F (annulusPoint q.1 q.2) := by
      rw [← integral_indicator hT]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        by_cases hq : q ∈ T
        · simp only [indicator_of_mem ((hmem q).mpr hq), indicator_of_mem hq]
          exact congrArg F (heq q)
        · simp only [indicator_of_notMem (mt (hmem q).mp hq), indicator_of_notMem hq]
    _ = _ := setIntegral_prod _ hInt

/-- Remove the null annular boundary and compute the actual continuous scalar integral
iteratively. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusInteriorIntegral_eq_iterated (F : LoopPlane → ℝ) (hF : Continuous F) :
    (∫ p in interior m64AnnulusDomain, F p) =
      ∫ x in Icc (0 : ℝ) curvePeriod, ∫ s in Icc (0 : ℝ) 1, F (annulusPoint x s) := by
  rw [← setIntegral_congr_set m64AnnulusDomain_ae_eq_interior]
  exact m64AnnulusIntegral_eq_iterated F hF

end PoincareMT
