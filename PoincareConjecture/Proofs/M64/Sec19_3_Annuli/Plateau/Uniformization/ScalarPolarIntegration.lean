import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverJacobian
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open Proofs.M58

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem polar_band_subset :
    Ioo (1 : ℝ) 2 ×ˢ Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
  intro p hp
  exact ⟨lt_trans zero_lt_one hp.1.1, hp.2⟩

private theorem polar_point_annulus {p : ℝ × ℝ}
    (hp : p ∈ Ioo (1 : ℝ) 2 ×ˢ Ioo (-Real.pi) Real.pi) :
    p.1 • angularPoint p.2 ∈ scalarAnnulus := by
  have hr : 0 < p.1 := lt_trans zero_lt_one hp.1.1
  have hnorm : ‖p.1 • angularPoint p.2‖ = p.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularPoint, mul_one]
  simpa only [scalarAnnulus, mem_ofPred_eq, hnorm, mem_Ioo] using hp.1

theorem scalarAnnulus_integral_polar (F : Plane → ℝ) :
    (∫ x in scalarAnnulus, F x) =
      ∫ p in Ioo (1 : ℝ) 2 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * F (p.1 • angularPoint p.2) := by
  classical
  let S : Set (ℝ × ℝ) := Ioo (1 : ℝ) 2 ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Ioo.prod MeasurableSet.univ
  have hset : S ∩ polarCoord.target = Ioo (1 : ℝ) 2 ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [S, polarCoord_target, mem_inter_iff, mem_prod, mem_univ, and_true,
      mem_Ioi]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, lt_trans zero_lt_one h.1.1, h.2⟩
  rw [← integral_indicator scalarAnnulus_isOpen.measurableSet, ← integral_polar_loopPlane]
  calc
    _ = ∫ p in polarCoord.target,
        S.indicator (fun p => p.1 * F (p.1 • angularPoint p.2)) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hnorm : ‖p.1 • angularPoint p.2‖ = p.1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1, norm_angularPoint, mul_one]
      have hmem : p.1 • angularPoint p.2 ∈ scalarAnnulus ↔ p ∈ S := by
        simp only [scalarAnnulus, mem_ofPred_eq, hnorm, S, mem_prod, mem_Ioo, mem_univ,
          and_true]
      change p.1 * scalarAnnulus.indicator F (p.1 • angularPoint p.2) = _
      by_cases hpS : p ∈ S
      · rw [indicator_of_mem (hmem.mpr hpS), indicator_of_mem hpS]
      · rw [indicator_of_notMem (mt hmem.mp hpS), indicator_of_notMem hpS, mul_zero]
    _ = _ := by rw [integral_indicator hS, Measure.restrict_restrict hS, hset]

theorem scalarAnnulus_integrable_polar {F : Plane → ℝ}
    (hF : IntegrableOn F scalarAnnulus) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * F (p.1 • angularPoint p.2))
      (Ioo (1 : ℝ) 2 ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hI : Integrable (scalarAnnulus.indicator F) :=
    (integrable_indicator_iff scalarAnnulus_isOpen.measurableSet).mpr hF
  have hcomp := measurePreserving_loopPlaneEquivProd.symm.integrable_comp_of_integrable hI
  have hpolar := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn
    ((scalarAnnulus.indicator F) ∘ loopPlaneEquivProd.symm)).mp (by
      rw [polarCoord.symm_image_target_eq_source]
      exact hcomp.integrableOn)
  apply (hpolar.mono_set polar_band_subset).congr_fun ?_ (measurableSet_Ioo.prod measurableSet_Ioo)
  intro p hp
  simp only [Function.comp_def, det_fderivPolarCoordSymm,
    abs_of_pos (lt_trans zero_lt_one hp.1.1), smul_eq_mul,
    loopPlaneEquivProd_symm_polar, indicator_of_mem (polar_point_annulus hp)]

theorem scalarCoverMap_polar_relation (r theta : ℝ) :
    scalarCoverMap (r, theta / (2 * Real.pi)) = r • angularPoint theta := by
  have hpi : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hangle : 2 * Real.pi * (theta / (2 * Real.pi)) = theta := by
    exact mul_div_cancel₀ theta hpi
  ext i
  fin_cases i <;> simp [scalarCoverMap, scalarCirclePoint, angularPoint, hangle]

end PoincareConjecture.M64Uniformization
