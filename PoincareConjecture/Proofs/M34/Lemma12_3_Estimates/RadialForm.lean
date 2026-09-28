import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.AxisForm
import PoincareConjecture.Proofs.M34.Standard.RotationOrbit
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean












set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M34



noncomputable def initialRadialCoefficient (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  g₀.metric.inner (EuclideanSpace.single (0 : Fin 3) r)
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))



noncomputable def initialAngularCoefficient (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  g₀.metric.inner (EuclideanSpace.single (0 : Fin 3) r)
    (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))



theorem initialAxisCoefficient_contDiff (g₀ : StandardInitialMetric) (i : Fin 3) :
    ContDiff ℝ ∞ (fun r : ℝ => g₀.metric.inner (EuclideanSpace.single (0 : Fin 3) r)
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))) := by
  have hmetric := contDiff_iff_contDiffAt.mpr g₀.metric.contDiffAt_euclideanCoefficients
  have haxis : ContDiff ℝ ∞ (fun r : ℝ => EuclideanSpace.single (0 : Fin 3) r) := by
    have h : ContDiff ℝ ∞ (fun r : ℝ => r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
      contDiff_id.smul contDiff_const
    convert! h using 1
    funext r
    ext j
    simp
  exact ((hmetric.comp haxis).clm_apply contDiff_const).clm_apply contDiff_const



theorem initialRadialCoefficient_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (initialRadialCoefficient g₀) := initialAxisCoefficient_contDiff g₀ 0



theorem initialAngularCoefficient_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (initialAngularCoefficient g₀) := initialAxisCoefficient_contDiff g₀ 1



theorem initialCoefficients_pos (g₀ : StandardInitialMetric) (r : ℝ) :
    0 < initialRadialCoefficient g₀ r ∧ 0 < initialAngularCoefficient g₀ r := by
  constructor
  · exact g₀.metric.pos _ _ (show EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ≠
      (0 : StandardCapSpace) by simp)
  · exact g₀.metric.pos _ _ (show EuclideanSpace.single (1 : Fin 3) (1 : ℝ) ≠
      (0 : StandardCapSpace) by simp)

set_option backward.isDefEq.respectTransparency false in


theorem initialCoefficients_zero (g₀ : StandardInitialMetric) :
    initialRadialCoefficient g₀ 0 = initialAngularCoefficient g₀ 0 := by
  let b := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
  obtain ⟨A, hA⟩ := exists_standardRotation_axis (b 1)
  have hA0 : standardRotation A (b 0) = b 1 := by simpa [b] using hA
  have hz : standardRotation A 0 = 0 := (capRotationIsometry A).map_zero
  have h := initialMetric_inner_rotation g₀ A 0 (b 0) (b 0)
  erw [hz, hA0] at h
  unfold initialRadialCoefficient initialAngularCoefficient
  erw [show EuclideanSpace.single (0 : Fin 3) (0 : ℝ) = 0 by simp]
  exact h.symm

set_option backward.isDefEq.respectTransparency false in


theorem initialMetric_radial_inner (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    g₀.metric.inner x u v = initialAngularCoefficient g₀ ‖x‖ * inner ℝ u v +
      ((initialRadialCoefficient g₀ ‖x‖ - initialAngularCoefficient g₀ ‖x‖) / ‖x‖ ^ 2) *
        inner ℝ x u * inner ℝ x v := by
  obtain ⟨A, hAx⟩ := exists_standardRotation_axis x
  have hsurj : Function.Surjective (capRotationIsometry A) :=
    LinearMap.injective_iff_surjective.mp (capRotationIsometry A).injective
  obtain ⟨U, hU⟩ := hsurj u
  obtain ⟨V, hV⟩ := hsurj v
  change standardRotation A U = u at hU
  change standardRotation A V = v at hV
  have hmetric := initialMetric_inner_rotation g₀ A (EuclideanSpace.single 0 ‖x‖) U V
  erw [hAx, hU, hV, initialMetric_axis_inner] at hmetric
  change g₀.metric.inner x u v = initialRadialCoefficient g₀ ‖x‖ * U 0 * V 0 +
    initialAngularCoefficient g₀ ‖x‖ * (U 1 * V 1 + U 2 * V 2) at hmetric
  have hxu := standardRotation_inner A (EuclideanSpace.single 0 ‖x‖) U
  have hxv := standardRotation_inner A (EuclideanSpace.single 0 ‖x‖) V
  rw [hAx, hU, EuclideanSpace.inner_single_left] at hxu
  rw [hAx, hV, EuclideanSpace.inner_single_left] at hxv
  have huv := standardRotation_inner A U V
  rw [hU, hV] at huv
  have huv' : inner ℝ u v = U 0 * V 0 + U 1 * V 1 + U 2 * V 2 := by
    rw [huv]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      dotProduct, Fin.sum_univ_three]
    ring
  rw [hmetric, huv', hxu, hxv]
  simp only [starRingEnd_apply, star_trivial]
  field_simp [norm_ne_zero_iff.mpr hx]
  ring

end PoincareConjecture.M34
