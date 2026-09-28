import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Volume

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

section Normalization

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem AncientKappaNormalization.core_volume_zero
    (N : AncientKappaNormalization K p 0) (D : ℝ) :
    calibratedMetricVolume (N.target.flow.metric 0)
        ((N.target.flow.metric 0).ball p D) =
      ENNReal.ofReal (N.scale ^ (3 / 2 : ℝ)) *
        calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p (D * N.scale ^ (-1 / 2 : ℝ))) := by
  have hmetric : MetricHomothety (K.flow.metric 0) (N.target.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) N.scale := by
    intro x v w
    simpa [Diffeomorph.coe_refl, mfderiv_id] using N.metric_eq 0 x v w
  have hradius : Real.sqrt N.scale * (D * N.scale ^ (-1 / 2 : ℝ)) = D := by
    rw [Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg N.scale_pos.le, mul_left_comm,
      mul_inv_cancel₀ (Real.rpow_pos_of_pos N.scale_pos (1 / 2 : ℝ)).ne', mul_one]
  have hball : (K.flow.metric 0).ball p (D * N.scale ^ (-1 / 2 : ℝ)) =
      (N.target.flow.metric 0).ball p D := by
    simpa only [Diffeomorph.coe_refl, Set.image_id, id_eq, Set.image_id', hradius] using
      Homothety.homothety_ball_image (K.flow.metric 0) (N.target.flow.metric 0)
        (Diffeomorph.refl (𝓡 3) M ∞) N.scale N.scale_pos hmetric p
        (D * N.scale ^ (-1 / 2 : ℝ))
  have hvolume := Homothety.homothety_volume_image
    (K.flow.metric 0) (N.target.flow.metric 0)
    (Diffeomorph.refl (𝓡 3) M ∞) N.scale N.scale_pos hmetric
    ((K.flow.metric 0).ball p (D * N.scale ^ (-1 / 2 : ℝ)))
  simpa only [Diffeomorph.coe_refl, Set.image_id, hball, Nat.cast_ofNat,
    Real.rpow_eq_pow] using hvolume

theorem AncientKappaNormalization.core_volume_bounds_zero
    (N : AncientKappaNormalization K p 0) {D v V : ℝ}
    (hvolume :
      ENNReal.ofReal v < calibratedMetricVolume (N.target.flow.metric 0)
        ((N.target.flow.metric 0).ball p D) ∧
      calibratedMetricVolume (N.target.flow.metric 0)
        ((N.target.flow.metric 0).ball p D) < ENNReal.ofReal V) :
    ENNReal.ofReal (v * N.scale ^ (-3 / 2 : ℝ)) <
        calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p (D * N.scale ^ (-1 / 2 : ℝ))) ∧
      calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p (D * N.scale ^ (-1 / 2 : ℝ))) <
        ENNReal.ofReal (V * N.scale ^ (-3 / 2 : ℝ)) := by
  have hfactor : ENNReal.ofReal (N.scale ^ (3 / 2 : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos N.scale_pos _)).ne'
  have hcancel (a : ℝ) :
      ENNReal.ofReal (N.scale ^ (3 / 2 : ℝ)) *
        ENNReal.ofReal (a * N.scale ^ (-3 / 2 : ℝ)) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg N.scale_pos.le _)]
    congr 1
    rw [mul_left_comm, ← Real.rpow_add N.scale_pos]
    norm_num
  constructor
  · apply (ENNReal.mul_lt_mul_iff_right hfactor ENNReal.ofReal_ne_top).mp
    rw [hcancel, ← N.core_volume_zero D]
    exact hvolume.1
  · apply (ENNReal.mul_lt_mul_iff_right hfactor ENNReal.ofReal_ne_top).mp
    rw [hcancel, ← N.core_volume_zero D]
    exact hvolume.2

end Normalization

theorem noncompact_core_uniform_scaled_volume_bounds_of_services
    (P : NoncompactKappaServices.{u})
    {D : ℝ} (hD : 1 < D) :
    ∃ v V : ℝ, 0 < v ∧ 0 < V ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ENNReal.ofReal (v * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) <
          calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) ∧
        calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) <
          ENNReal.ofReal (V * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨v, V, hv, hV, hbound⟩ :=
    noncompact_core_fixed_kappa_normalized_volume_bounds_of_services P hkappa hD
  refine ⟨v, V, hv, hV, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnonround
  let L : AncientKappaSolution 3 M := {
    K with
    kappa := kappa
    kappa_pos := hkappa
    noncollapsed := hnoncollapsed K hnonround
  }
  obtain ⟨N⟩ := P.normalization M L p 0 le_rfl
  have htarget : AncientKappaNoncollapsed N.target.flow kappa := by
    have hk : N.target.kappa = kappa := N.target_kappa
    rw [← hk]
    exact N.target.noncollapsed
  have hnormalized := hbound N.target p htarget N.normalized_scalar
  have hscaled := N.core_volume_bounds_zero hnormalized
  simpa only [N.scale_eq, L] using hscaled

theorem noncompact_core_uniform_scaled_volume_bounds
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {D : ℝ} (hD : 1 < D) :
    ∃ v V : ℝ, 0 < v ∧ 0 < V ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        ENNReal.ofReal (v * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) <
          calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) ∧
        calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) <
          ENNReal.ofReal (V * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) := by
  exact noncompact_core_uniform_scaled_volume_bounds_of_services P.noncompactServices hD

end PoincareConjecture
