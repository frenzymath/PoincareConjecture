import PoincareConjecture.Proofs.M03.Existence.ChartLpNative
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import Mathlib.Analysis.SpecialFunctions.PolarCoord

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace PoincareConjecture.M65Interior

def polarMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict polarCoord.target).withDensity (fun p => ENNReal.ofReal p.1)

theorem polar_measurePreserving :
    MeasurePreserving polarCoord.symm polarMeasure volume := by
  refine ⟨continuous_polarCoord_symm.measurable, ?_⟩
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar volume
    polarCoord.open_target.measurableSet.nullMeasurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt) polarCoord.symm.injOn
  have hweight : (volume.restrict polarCoord.target).withDensity
      (fun p => ENNReal.ofReal |(fderivPolarCoordSymm p).det|) = polarMeasure := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]
  rw [hweight, polarCoord.symm_image_target_eq_source,
    Measure.restrict_congr_set polarCoord_source_ae_eq_univ, Measure.restrict_univ] at hmap
  exact hmap

theorem polar_strip_measure_le {ε R : ℝ} (hε : 0 < ε) :
    (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi)) ≤
      (ENNReal.ofReal ε)⁻¹ • polarMeasure := by
  let K := Icc ε R ×ˢ Ioo (-Real.pi) Real.pi
  have hK : MeasurableSet K := measurableSet_Icc.prod measurableSet_Ioo
  have hKU : K ⊆ polarCoord.target := fun p hp => ⟨hε.trans_le hp.1.1, hp.2⟩
  have hstrip :
      (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi)) =
        volume.restrict K := by
    rw [Measure.prod_restrict]
    exact Measure.restrict_congr_set
      (Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _)
        (Ioo_ae_eq_Icc (α := ℝ) (μ := volume)).symm)
  rw [hstrip]
  apply ChartLpNative.le_inv_smul_of_smul_le
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top
  calc
    _ = (volume.restrict K).withDensity (fun _ => ENNReal.ofReal ε) :=
      (withDensity_const _).symm
    _ ≤ (volume.restrict K).withDensity (fun p => ENNReal.ofReal p.1) := by
      apply withDensity_mono
      filter_upwards [ae_restrict_mem hK] with p hp
      exact ENNReal.ofReal_le_ofReal hp.1.1
    _ = polarMeasure.restrict K := by
      rw [polarMeasure, restrict_withDensity hK, Measure.restrict_restrict hK,
        inter_eq_left.mpr hKU]
    _ ≤ polarMeasure := Measure.restrict_le_self

def polarPlane (x : LoopPlane) (p : ℝ × ℝ) : LoopPlane :=
  x + p.1 • Proofs.M58.angularPoint p.2

theorem polarPlane_measurePreserving (x : LoopPlane) :
    MeasurePreserving (polarPlane x) polarMeasure volume := by
  change MeasurePreserving (fun p : ℝ × ℝ => x + p.1 • Proofs.M58.angularPoint p.2)
    polarMeasure volume
  have h := (measurePreserving_add_left volume x).comp
    (Proofs.M58.measurePreserving_loopPlaneEquivProd.symm.comp polar_measurePreserving)
  simpa only [Function.comp_def, Proofs.M58.loopPlaneEquivProd_symm_polar] using h

theorem polarPlane_map_strip_le (x : LoopPlane) {ε R : ℝ} (hε : 0 < ε) :
    Measure.map (polarPlane x)
      ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) ≤
        (ENNReal.ofReal ε)⁻¹ • (volume : Measure LoopPlane) := by
  have h := Measure.map_mono (polar_strip_measure_le (R := R) hε)
    (polarPlane_measurePreserving x).measurable
  rwa [Measure.map_smul, (polarPlane_measurePreserving x).map_eq] at h

end PoincareConjecture.M65Interior
