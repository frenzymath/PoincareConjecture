import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.SlopeMonotonicity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in


theorem initialAxis_angular_orthonormal (g₀ : StandardInitialMetric) (r : ℝ) :
    let α := (Real.sqrt (initialAngularCoefficient g₀ r))⁻¹
    LeviCivitaData.IsOrthonormalPair g₀.metric (EuclideanSpace.single (0 : Fin 3) r)
      (α • EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (α • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
  let x : StandardCapSpace := EuclideanSpace.single 0 r
  let b := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
  let c := initialAngularCoefficient g₀ r
  let α := (Real.sqrt c)⁻¹
  have hc : 0 < c := (initialCoefficients_pos g₀ r).2
  have h11 : B (b 1) (b 1) = c := rfl
  have h12 : B (b 1) (b 2) = 0 := (initialMetric_axis_coefficients g₀ r).2.2.1
  have h22 : B (b 2) (b 2) = c := (initialMetric_axis_coefficients g₀ r).2.2.2
  have hs : α * (α * c) = 1 := by
    dsimp [α]
    field_simp [(Real.sqrt_pos.mpr hc).ne']
    exact (Real.sq_sqrt hc.le).symm
  change B (α • b 1) (α • b 1) = 1 ∧
    B (α • b 2) (α • b 2) = 1 ∧ B (α • b 1) (α • b 2) = 0
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_smul, smul_apply, smul_eq_mul, h11] using hs
  · simpa only [map_smul, smul_apply, smul_eq_mul, h22] using hs
  · simp only [map_smul, smul_apply, smul_eq_mul, h12, mul_zero]

set_option backward.isDefEq.respectTransparency false in


theorem initialTip_angular_positive (g₀ : StandardInitialMetric) {R r : ℝ}
    (htip : ∀ x ∈ g₀.metric.ball 0 R, ∀ u v,
      LeviCivitaData.IsOrthonormalPair g₀.metric x u v →
        g₀.connection.sectionalCurvature x u v = (1 / 4 : ℝ))
    (hr : EuclideanSpace.single (0 : Fin 3) r ∈ g₀.metric.ball 0 R) :
    0 < g₀.connection.curvatureTensor (EuclideanSpace.single (0 : Fin 3) r)
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
  let x : StandardCapSpace := EuclideanSpace.single 0 r
  let u : StandardCapSpace := EuclideanSpace.single 1 1
  let v : StandardCapSpace := EuclideanSpace.single 2 1
  let α := (Real.sqrt (initialAngularCoefficient g₀ r))⁻¹
  have hα : 0 < α := inv_pos.mpr (Real.sqrt_pos.mpr (initialCoefficients_pos g₀ r).2)
  have ho : LeviCivitaData.IsOrthonormalPair g₀.metric x (α • u) (α • v) :=
    initialAxis_angular_orthonormal g₀ r
  have h := htip x hr (α • u) (α • v) ho
  unfold LeviCivitaData.sectionalCurvature at h
  rw [ho.1, ho.2.1, ho.2.2] at h
  norm_num at h
  have hp : 0 < g₀.connection.curvatureTensor x (α • u) (α • v) (α • u) (α • v) := by
    rw [h]
    norm_num
  rw [g₀.connection.curvatureTensor_smul_first,
    g₀.connection.curvatureTensor_smul_second,
    g₀.connection.curvatureTensor_smul_third,
    g₀.connection.curvatureTensor_smul_last] at hp
  simpa only [mul_pos_iff_of_pos_left hα] using hp



theorem initialTip_angular_positive_segment (g₀ : StandardInitialMetric) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 ≤ r → r < δ →
      0 < g₀.connection.curvatureTensor (EuclideanSpace.single (0 : Fin 3) r)
        (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
        (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
        (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
        (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
  obtain ⟨R, hR, htip⟩ := g₀.tip_sectional_curvature
  have hz : initialRadialLength g₀ 0 = 0 := by simp [initialRadialLength]
  have he : {r : ℝ | initialRadialLength g₀ r < R} ∈ 𝓝 0 :=
    (initialRadialLength_hasDerivAt g₀ 0).continuousAt
      (Iio_mem_nhds (by rw [hz]; exact hR))
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, fun r hr hrδ => initialTip_angular_positive g₀ htip ?_⟩
  have hlen : initialRadialLength g₀ r < R := hsub (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hr] using hrδ)
  exact (initialAxis_edist_le_radialLength g₀ hr).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hlen)

end PoincareConjecture.M34
