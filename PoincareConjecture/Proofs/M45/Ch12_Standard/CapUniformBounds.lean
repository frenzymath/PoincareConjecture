import PoincareConjecture.Proofs.M45.Ch12_Standard.CanonicalConstants









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.StandardCapNeighborhood

variable {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
  {F : MaximalStandardCapFlow g₀} {t epsilon C : ℝ} {x : StandardCapSpace}



theorem intrinsicDiameter_lt_add_one
    (N : StandardCapNeighborhood atlas F t epsilon C x) :
    intrinsicDiameter (F.metric t) N.carrier <
      ENNReal.ofReal ((C + 1) *
        scalarCurvatureSupOn (F.metric t) (F.connection t) N.carrier ^ (-1 / 2 : ℝ)) := by
  have hp := Real.rpow_pos_of_pos N.scalarSup_pos (-1 / 2 : ℝ)
  have hdiam : intrinsicDiameter (F.metric t) N.carrier ≤
      ENNReal.ofReal (C *
        scalarCurvatureSupOn (F.metric t) (F.connection t) N.carrier ^ (-1 / 2 : ℝ)) := by
    apply sSup_le
    rintro _ ⟨⟨y, z⟩, rfl⟩
    exact (N.diameter_bound y.1 y.2 z.1 z.2).le
  apply hdiam.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by linarith [N.constant_pos]) hp)).2
  nlinarith



theorem scalarRatio_uniform (N : StandardCapNeighborhood atlas F t epsilon C x) :
    ∃ bound : ℝ, bound < C + 1 ∧ ∀ y ∈ N.carrier, ∀ z ∈ N.carrier,
      (F.connection t).scalarCurvature z ≤ bound * (F.connection t).scalarCurvature y := by
  exact ⟨C, by linarith, fun y hy z hz => (N.scalar_ratio y hy z hz).le⟩



theorem volume_lt_add_one (N : StandardCapNeighborhood atlas F t epsilon C x) :
    calibratedMetricVolume (F.metric t) N.carrier < ENNReal.ofReal (C + 1) *
      ENNReal.ofReal
        (scalarCurvatureSupOn (F.metric t) (F.connection t) N.carrier ^ (-3 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_mul (by linarith [N.constant_pos] : 0 ≤ C + 1)]
  exact N.volume_bound.trans_le (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
      (Real.rpow_nonneg N.scalarSup_pos.le _)))



theorem exists_uniform_coreRadii (N : StandardCapNeighborhood atlas F t epsilon C x) :
    ∃ radius : StandardCapSpace → ℝ,
      (∀ y ∈ interior N.closed_core, 0 < radius y) ∧
      (∀ y ∈ interior N.closed_core,
        scalarCurvatureSupOn (F.metric t) (F.connection t)
          ((F.metric t).ball y (radius y)) = (radius y)⁻¹ ^ 2) ∧
      (∀ y ∈ interior N.closed_core,
        closure ((F.metric t).ball y (radius y)) ⊆ N.carrier) ∧
      (∀ y ∈ interior N.closed_core,
        IsCompact (closure ((F.metric t).ball y (radius y)))) ∧
      ∃ bound : ℝ, (C + 1)⁻¹ < bound ∧
        ∀ y ∈ interior N.closed_core,
          ENNReal.ofReal (bound * radius y ^ 3) ≤
            calibratedMetricVolume (F.metric t) ((F.metric t).ball y (radius y)) := by
  classical
  let radius : StandardCapSpace → ℝ := fun y =>
    if hy : y ∈ interior N.closed_core then (N.core_ball y hy).choose else 1
  have hspec (y : StandardCapSpace) (hy : y ∈ interior N.closed_core) :
      0 < radius y ∧
      scalarCurvatureSupOn (F.metric t) (F.connection t)
        ((F.metric t).ball y (radius y)) = (radius y)⁻¹ ^ 2 ∧
      closure ((F.metric t).ball y (radius y)) ⊆ N.carrier ∧
      IsCompact (closure ((F.metric t).ball y (radius y))) ∧
      ENNReal.ofReal (C⁻¹ * radius y ^ 3) <
        calibratedMetricVolume (F.metric t) ((F.metric t).ball y (radius y)) := by
    simpa only [radius, dif_pos hy] using (N.core_ball y hy).choose_spec
  refine ⟨radius, fun y hy => (hspec y hy).1, fun y hy => (hspec y hy).2.1,
    fun y hy => (hspec y hy).2.2.1, fun y hy => (hspec y hy).2.2.2.1,
    C⁻¹, ?_, fun y hy => (hspec y hy).2.2.2.2.le⟩
  exact (inv_lt_inv₀ (by linarith [N.constant_pos]) N.constant_pos).2 (by linarith)



theorem gradient_uniform (N : StandardCapNeighborhood atlas F t epsilon C x) :
    ∃ bound : ℝ, bound < C + 1 ∧ ∀ y ∈ N.carrier,
      scalarGradientNorm (F.metric t) (F.connection t) y ≤
        bound * (F.connection t).scalarCurvature y ^ (3 / 2 : ℝ) := by
  exact ⟨C, by linarith, fun y hy => (N.gradient_bound y hy).le⟩



theorem scalarEvolution_uniform (N : StandardCapNeighborhood atlas F t epsilon C x) :
    ∃ bound : ℝ, bound < C + 1 ∧ ∀ y ∈ N.carrier,
      |(F.connection t).laplacian (F.connection t).scalarCurvature y +
        2 * (F.connection t).ricciNormSq y| ≤
          bound * (F.connection t).scalarCurvature y ^ 2 := by
  exact ⟨C, by linarith, fun y hy => (N.time_derivative_bound y hy).le⟩

end PoincareConjecture.StandardCapNeighborhood
