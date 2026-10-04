import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Measure
import PoincareLib.Geometry.Riemannian.Measure.Balls
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product volume and axial integrals on the round cylinder

The fixed linear rechart preserves the product metric of twice the unit-sphere
metric and the Euclidean line metric. The actual intrinsic cylinder measure
is therefore the product of the scaled sphere volume and Lebesgue measure.
Its cross-sectional area is positive and finite, and axial profile integrals
factor through that area.

Reference: Morgan--Tian, Definitions 2.17--2.18 and Proposition 2.19,
pp. 30--32.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareMT

/-- The actual Riemannian area measure of a cross-section of the
scalar-normalized round cylinder. -/
def roundCylinderCrossSectionVolumeMeasure : Measure UnitTwoSphere :=
  (rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
    2 (by norm_num)).volumeMeasure

/-- The area of a cross-section of the scalar-normalized round cylinder. -/
def roundCylinderCrossSectionArea : ℝ≥0∞ :=
  roundCylinderCrossSectionVolumeMeasure univ

/-- The actual intrinsic round-cylinder measure is the product of its
scaled-sphere area measure and Lebesgue measure on the axial coordinate. -/
theorem roundCylinderVolumeMeasure_eq_prod :
    roundCylinderVolumeMeasure = roundCylinderCrossSectionVolumeMeasure.prod volume := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let h : RiemannianMetric 2 UnitTwoSphere :=
    rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
      2 (by norm_num)
  let e := roundCylinderModelDiffeomorph
  have hmetric : ∀ (z : UnitTwoSphere × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      roundCylinderMetric.inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
      h.inner z.1 v.1 w.1 + v.2 * w.2 := by
    intro z v w
    rw [roundCylinderMetric_inner]
    change EvolvingRoundCylinderMetric 0 z v w =
      (rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
        2 (by norm_num)).inner z.1 v.1 w.1 + v.2 * w.2
    rw [rescaledMetric_inner,
      Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner]
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one,
      RiemannianMetric.euclideanMetric_inner]
  have hpres := h.measurePreserving_productIsometry roundCylinderMetric e hmetric
  have he : (e : RoundCylinderSpace → RoundCylinderSpace) = id := rfl
  simpa only [he, Measure.map_id, roundCylinderVolumeMeasure,
    roundCylinderCrossSectionVolumeMeasure, h] using hpres.map_eq.symm

/-- The scaled unit sphere has positive intrinsic area. -/
theorem roundCylinderCrossSectionArea_pos : 0 < roundCylinderCrossSectionArea := by
  let h : RiemannianMetric 2 UnitTwoSphere :=
    rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
      2 (by norm_num)
  obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty
    (E := EuclideanSpace ℝ (Fin 3)) (x := 0) (r := 1)).mpr zero_le_one
  let q : UnitTwoSphere := ⟨x, hx⟩
  exact (h.volumeMeasure_ball_pos q (R := 1) zero_lt_one).trans_le
    (measure_mono (subset_univ _))

/-- Compactness of the actual scaled sphere gives finite cross-sectional area. -/
theorem roundCylinderCrossSectionArea_lt_top : roundCylinderCrossSectionArea < ⊤ := by
  exact (rescaledMetric (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2)
    2 (by norm_num)).volumeMeasure_lt_top_of_isCompact isCompact_univ

/-- The real-valued cross-sectional area is strictly positive. -/
theorem roundCylinderCrossSectionArea_toReal_pos :
    0 < roundCylinderCrossSectionArea.toReal :=
  ENNReal.toReal_pos roundCylinderCrossSectionArea_pos.ne'
    roundCylinderCrossSectionArea_lt_top.ne

/-- Integrating a nonnegative measurable axial profile over any cylinder
slice factors as cross-sectional area times the one-dimensional integral. -/
theorem lintegral_roundCylinder_axial_profile
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) (S : Set ℝ) :
    (∫⁻ z in (univ : Set UnitTwoSphere) ×ˢ S,
      F z.2 ∂roundCylinderVolumeMeasure) =
      roundCylinderCrossSectionArea * ∫⁻ t in S, F t := by
  let : IsFiniteMeasure roundCylinderCrossSectionVolumeMeasure :=
    ⟨roundCylinderCrossSectionArea_lt_top⟩
  rw [roundCylinderVolumeMeasure_eq_prod,
    setLIntegral_prod (fun z : UnitTwoSphere × ℝ => F z.2)
      (hF.comp measurable_snd).aemeasurable]
  simp only [Measure.restrict_univ, lintegral_const,
    roundCylinderCrossSectionArea, mul_comm]

/-- Real-valued axial profile integrals factor through the same actual
cross-sectional area. -/
theorem integral_roundCylinder_axial_profile (F : ℝ → ℝ) (S : Set ℝ) :
    (∫ z in (univ : Set UnitTwoSphere) ×ˢ S,
      F z.2 ∂roundCylinderVolumeMeasure) =
      roundCylinderCrossSectionArea.toReal * ∫ t in S, F t := by
  let : IsFiniteMeasure roundCylinderCrossSectionVolumeMeasure :=
    ⟨roundCylinderCrossSectionArea_lt_top⟩
  rw [roundCylinderVolumeMeasure_eq_prod]
  have h := setIntegral_prod_mul (μ := roundCylinderCrossSectionVolumeMeasure)
    (ν := volume) (fun _ : UnitTwoSphere => (1 : ℝ)) F univ S
  simpa only [one_mul, Measure.restrict_univ, integral_const, smul_eq_mul,
    mul_one, measureReal_def, roundCylinderCrossSectionArea] using h

end PoincareMT
