import PoincareConjecture.Proofs.M36.RadialCompleteness
import PoincareConjecture.Proofs.M36.RotationTransitivity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inverse










set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.M36

theorem axisRadialCoefficient_neg (g₀ : StandardInitialMetric) (r : ℝ) :
    axisRadialCoefficient g₀ (-r) = axisRadialCoefficient g₀ r := by
  obtain ⟨L, hdet, hL⟩ := exists_axis_isometry (-axisBasis 0) (by simp [axisBasis])
  have hp : L (axisPoint r) = axisPoint (-r) := by
    rw [axisPoint_eq_smul, map_smul, hL, axisPoint_eq_smul]
    simp
  have h := standardInitialMetric_isometry_inner g₀ L hdet
    (axisPoint r) (axisBasis 0) (axisBasis 0)
  rw [hp, hL] at h
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
    g₀.metric.inner (axisPoint (-r))
  change B (-axisBasis 0) (-axisBasis 0) = axisRadialCoefficient g₀ r at h
  change B (axisBasis 0) (axisBasis 0) = axisRadialCoefficient g₀ r
  simpa only [map_neg, neg_apply, neg_neg] using h

theorem radialSpeed_neg (g₀ : StandardInitialMetric) (r : ℝ) :
    radialSpeed g₀ (-r) = radialSpeed g₀ r := by
  simp only [radialSpeed, axisRadialCoefficient_neg]

theorem radialArclength_neg (g₀ : StandardInitialMetric) (r : ℝ) :
    radialArclength g₀ (-r) = -radialArclength g₀ r := by
  have h := intervalIntegral.integral_comp_neg (f := radialSpeed g₀) (a := 0) (b := r)
  simp only [radialSpeed_neg, neg_zero] at h
  unfold radialArclength
  rw [intervalIntegral.integral_symm (-r) 0, ← h]

theorem radialArclength_tendsto_atBot (g₀ : StandardInitialMetric) :
    Tendsto (radialArclength g₀) atBot atBot := by
  have h := tendsto_neg_atTop_atBot.comp
    ((radialArclength_tendsto_atTop g₀).comp tendsto_neg_atBot_atTop)
  simpa only [Function.comp_def, radialArclength_neg, neg_neg] using h

theorem radialArclength_surjective (g₀ : StandardInitialMetric) :
    Function.Surjective (radialArclength g₀) :=
  (radialArclength_contDiff g₀).continuous.surjective
    (radialArclength_tendsto_atTop g₀) (radialArclength_tendsto_atBot g₀)

noncomputable def radialArclengthOrderIso (g₀ : StandardInitialMetric) : ℝ ≃o ℝ :=
  (radialArclength_strictMono g₀).orderIsoOfSurjective
    (radialArclength g₀) (radialArclength_surjective g₀)

noncomputable def radialEuclideanRadius (g₀ : StandardInitialMetric) : ℝ → ℝ :=
  (radialArclengthOrderIso g₀).symm

theorem radialEuclideanRadius_arclength (g₀ : StandardInitialMetric) (r : ℝ) :
    radialEuclideanRadius g₀ (radialArclength g₀ r) = r :=
  (radialArclengthOrderIso g₀).symm_apply_apply r

theorem radialArclength_euclideanRadius (g₀ : StandardInitialMetric) (s : ℝ) :
    radialArclength g₀ (radialEuclideanRadius g₀ s) = s :=
  (radialArclengthOrderIso g₀).apply_symm_apply s

theorem radialEuclideanRadius_zero (g₀ : StandardInitialMetric) :
    radialEuclideanRadius g₀ 0 = 0 := by
  simpa only [radialArclength_zero] using radialEuclideanRadius_arclength g₀ 0

theorem radialEuclideanRadius_strictMono (g₀ : StandardInitialMetric) :
    StrictMono (radialEuclideanRadius g₀) :=
  (radialArclengthOrderIso g₀).symm.strictMono

theorem radialEuclideanRadius_pos_iff (g₀ : StandardInitialMetric) (s : ℝ) :
    0 < radialEuclideanRadius g₀ s ↔ 0 < s := by
  simpa only [radialEuclideanRadius_zero] using
    (radialEuclideanRadius_strictMono g₀).lt_iff_lt (a := 0) (b := s)

theorem radialEuclideanRadius_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (radialEuclideanRadius g₀) :=
  (radialArclengthOrderIso g₀).toHomeomorph.contDiff_symm_deriv
    (fun r => (radialSpeed_pos g₀ r).ne') (radialArclength_hasDerivAt g₀)
    (radialArclength_contDiff g₀)

theorem radialEuclideanRadius_hasDerivAt (g₀ : StandardInitialMetric) (s : ℝ) :
    HasDerivAt (radialEuclideanRadius g₀)
      (radialSpeed g₀ (radialEuclideanRadius g₀ s))⁻¹ s :=
  (radialArclength_hasDerivAt g₀ (radialEuclideanRadius g₀ s)).of_local_left_inverse
    (radialEuclideanRadius_contDiff g₀).continuous.continuousAt
    (radialSpeed_pos g₀ _).ne'
    (Filter.Eventually.of_forall (radialArclength_euclideanRadius g₀))

end PoincareConjecture.M36
