import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Comparison
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.ModelVolume
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Weighted volume comparison in actual neck coordinates

The metric-jet volume bounds compare the carrier volume transported by the
specified coordinate inverse with the restricted cylinder volume measure.
Consequently the same exact factors bound the integral of every measurable
nonnegative profile, including profiles with infinite integral.

Reference: Morgan--Tian, Proposition 2.19, pp. 31--32.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

omit [T2Space M] in
/-- Transporting carrier volume by the actual coordinate inverse evaluates
on a measurable cylinder set as the volume of its image inside the neck. -/
theorem map_coordinate_inverse_volumeMeasure_apply
    {A : Set RoundCylinderSpace} (hA : MeasurableSet A) :
    ((g.volumeMeasure.restrict N.carrier).map N.coordinate_inverse) A =
      g.volumeMeasure (N.coordinate_map '' (A ∩ N.cylinderDomain)) := by
  have hm : AEMeasurable N.coordinate_inverse (g.volumeMeasure.restrict N.carrier) :=
    N.coordinate_inverse_smooth.continuousOn.aemeasurable N.carrier_open.measurableSet
  rw [Measure.map_apply_of_aemeasurable hm hA,
    Measure.restrict_apply' N.carrier_open.measurableSet]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨N.coordinate_inverse x, ⟨hx.1, N.coordinate_inverse_mem x hx.2⟩,
      N.coordinate_map_coordinate_inverse hx.2⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨by simpa only [mem_preimage, N.coordinate_inverse_coordinate_map hz.2] using hz.1,
      N.coordinate_map_mem hz.2⟩

/-- The actual inverse-coordinate transport of neck volume is bounded above
and below by the cylinder volume with the factors from the neck metric jet. -/
theorem map_coordinate_inverse_volumeMeasure_bounds :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 •
        (roundCylinderVolumeMeasure.restrict N.cylinderDomain) ≤
      (g.volumeMeasure.restrict N.carrier).map N.coordinate_inverse ∧
      (g.volumeMeasure.restrict N.carrier).map N.coordinate_inverse ≤
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 •
          (roundCylinderVolumeMeasure.restrict N.cylinderDomain) := by
  constructor
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA,
      N.map_coordinate_inverse_volumeMeasure_apply hA]
    exact (N.volumeMeasure_image_bounds
      (hA.inter N.cylinderDomain_open.measurableSet) inter_subset_right).1
  · apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, Measure.restrict_apply hA,
      N.map_coordinate_inverse_volumeMeasure_apply hA]
    exact (N.volumeMeasure_image_bounds
      (hA.inter N.cylinderDomain_open.measurableSet) inter_subset_right).2

/-- Every measurable nonnegative cylinder profile satisfies the metric-jet
volume comparison when integrated through the actual neck coordinate inverse. -/
theorem lintegral_coordinate_inverse_bounds
    {F : RoundCylinderSpace → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (∫⁻ z in N.cylinderDomain, F z ∂roundCylinderVolumeMeasure) ≤
      ∫⁻ x in N.carrier, F (N.coordinate_inverse x) ∂g.volumeMeasure ∧
      (∫⁻ x in N.carrier, F (N.coordinate_inverse x) ∂g.volumeMeasure) ≤
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 *
          ∫⁻ z in N.cylinderDomain, F z ∂roundCylinderVolumeMeasure := by
  have hm : AEMeasurable N.coordinate_inverse (g.volumeMeasure.restrict N.carrier) :=
    N.coordinate_inverse_smooth.continuousOn.aemeasurable N.carrier_open.measurableSet
  have hmap := lintegral_map' hF.aemeasurable hm
  obtain ⟨hlower, hupper⟩ := N.map_coordinate_inverse_volumeMeasure_bounds
  constructor
  · have h := lintegral_mono' hlower (f := F) (g := F) (fun _ => le_rfl)
    simpa only [lintegral_smul_measure, smul_eq_mul, hmap] using h
  · have h := lintegral_mono' hupper (f := F) (g := F) (fun _ => le_rfl)
    simpa only [lintegral_smul_measure, smul_eq_mul, hmap] using h

/-- Axial profiles on an actual neck are bounded by its scalar-normalized
cross-sectional area times a one-dimensional integral, with exact jet factors. -/
theorem lintegral_axial_profile_bounds
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea *
          ∫⁻ t in Ioo (-N.epsilon⁻¹) N.epsilon⁻¹, F t) ≤
      ∫⁻ x in N.carrier, F (N.coordinate_inverse x).2 ∂g.volumeMeasure ∧
      (∫⁻ x in N.carrier, F (N.coordinate_inverse x).2 ∂g.volumeMeasure) ≤
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 *
          (roundCylinderCrossSectionArea *
            ∫⁻ t in Ioo (-N.epsilon⁻¹) N.epsilon⁻¹, F t) := by
  simpa only [Function.comp_def, cylinderDomain, lintegral_roundCylinder_axial_profile hF] using
    N.lintegral_coordinate_inverse_bounds (hF.comp measurable_snd)

end PoincareMT.EpsilonNeck
