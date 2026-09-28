import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderJetReadout
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapRatio

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds

theorem neck_normalized_scalar_center
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (D : LeviCivitaData g) :
    N.scale ^ 2 * D.scalarCurvature N.center = 1 := by
  have hscale : N.scale ^ 2 = (N.connection.scalarCurvature N.center)⁻¹ := by
    rw [N.scale_eq_scalar,
      ← Real.rpow_mul_natCast N.scalar_center_pos.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  rw [← N.connection.scalarCurvature_eq_m28 D N.center, hscale]
  exact inv_mul_cancel₀ N.scalar_center_pos.ne'

private theorem exists_cylinder_scalar_model_accuracy {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (N : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → ∀ x ∈ N.carrier,
          |N.scale ^ 2 * D.scalarCurvature x - jetScalarCurvature cylinderModelTwoJet| <
            delta := by
  obtain ⟨L, hL, hjet⟩ := exists_cylinder_metricTwoJet_bound.{u}
  obtain ⟨eta, heta, hmod⟩ := exists_cylinder_model_scalar_modulus hdelta
  let epsilon₀ := min (1 / 200 : ℝ) (eta / (2 * L))
  have hepsilon₀ : 0 < epsilon₀ := lt_min (by norm_num)
    (div_pos heta (mul_pos (by norm_num) hL))
  refine ⟨epsilon₀, hepsilon₀, min_le_left _ _, ?_⟩
  intro M _ _ _ _ g D N hsmall x hx
  have horder : 2 ≤ ⌊N.epsilon⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [inv_eq_one_div, le_div_iff₀ N.epsilon_pos]
    norm_num
    linarith [N.epsilon_lt_half]
  have hdist : L * N.epsilon < eta := by
    have h := hsmall.trans (min_le_right _ _)
    have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL)).mp h
    nlinarith
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have h := hmod _ ((hjet M g N horder z hz).trans_lt hdist)
  rw [cylinderNeckCoefficients_scalar_zero N D z.1 hz,
    N.coordinate_map_coordinate_inverse hx] at h
  exact h

theorem exists_cylinder_scalar_accuracy {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (N : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → ∀ x ∈ N.carrier,
          |N.scale ^ 2 * D.scalarCurvature x - 1| < delta := by
  obtain ⟨epsilon₀, hpos, hsmall, hclose⟩ :=
    exists_cylinder_scalar_model_accuracy.{u} (delta := delta / 2) (by positivity)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D N hepsilon x hx
  have hc := hclose M g D N hepsilon N.center
    (N.central_sphere_subset N.center_on_central_sphere)
  rw [neck_normalized_scalar_center N D] at hc
  calc
    |N.scale ^ 2 * D.scalarCurvature x - 1| ≤
        |N.scale ^ 2 * D.scalarCurvature x - jetScalarCurvature cylinderModelTwoJet| +
          |jetScalarCurvature cylinderModelTwoJet - 1| := abs_sub_le _ _ _
    _ < delta / 2 + delta / 2 :=
      add_lt_add (hclose M g D N hepsilon x hx) (by simpa only [abs_sub_comm] using hc)
    _ = delta := by ring

theorem exists_cylinder_scalar_ratio_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (N : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → ∀ x ∈ N.carrier, ∀ y ∈ N.carrier,
          D.scalarCurvature x ≤ 2 * D.scalarCurvature y := by
  obtain ⟨epsilon₀, hpos, hsmall, hclose⟩ :=
    exists_cylinder_scalar_accuracy.{u} (delta := 1 / 4) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D N hepsilon x hx y hy
  have hx' := abs_lt.mp (hclose M g D N hepsilon x hx)
  have hy' := abs_lt.mp (hclose M g D N hepsilon y hy)
  apply (mul_le_mul_iff_right₀ (pow_pos N.scale_pos 2)).mp
  nlinarith only [hx'.2, hy'.1]

end PoincareConjecture.M28.tube
