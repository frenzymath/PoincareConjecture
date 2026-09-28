import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.VolumeScaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem noncompact_uniform_core_upper_and_volume_of_services
    (P : NoncompactKappaServices.{u})
    {D : ℝ} (hD : 1 < D) :
    ∃ D₁ : ℝ, 1 < D₁ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsCompact (Set.univ : Set M) →
        (∀ x ∈ (K.flow.metric 0).ball p
            (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          ∀ a b : TangentSpace (𝓡 3) x,
            (K.flow.connection 0).sectionalCurvature x a b <
              D₁ * (K.flow.connection 0).scalarCurvature p) ∧
        ENNReal.ofReal
            (D₁ ^ (-3 / 2 : ℝ) * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) <
          calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) ∧
        calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) <
          ENNReal.ofReal
            (D₁ ^ (3 / 2 : ℝ) * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hcurvature⟩ := nonround_uniform_core_sectional_upper_of_services P
    (lt_trans zero_lt_one hD)
  obtain ⟨v, V, hv, _, hvolume⟩ := noncompact_core_uniform_scaled_volume_bounds_of_services P hD
  let D₁ : ℝ := max (max C v⁻¹) V + 1
  have hCD : C ≤ D₁ := by
    have h₁ := le_max_left C v⁻¹
    have h₂ := le_max_left (max C v⁻¹) V
    dsimp [D₁]
    linarith
  have hvD : v⁻¹ ≤ D₁ := by
    have h₁ := le_max_right C v⁻¹
    have h₂ := le_max_left (max C v⁻¹) V
    dsimp [D₁]
    linarith
  have hVD : V ≤ D₁ := by
    have := le_max_right (max C v⁻¹) V
    dsimp [D₁]
    linarith
  have hD₁ : 1 < D₁ := hC.trans_le hCD
  have hD₁pos : 0 < D₁ := lt_trans zero_lt_one hD₁
  have hpower : D₁ ≤ D₁ ^ (3 / 2 : ℝ) :=
    Real.self_le_rpow_of_one_le hD₁.le (by norm_num)
  have hlower : D₁ ^ (-3 / 2 : ℝ) ≤ v := by
    rw [neg_div, Real.rpow_neg hD₁pos.le]
    exact inv_le_of_inv_le₀ hv (hvD.trans hpower)
  have hupper : V ≤ D₁ ^ (3 / 2 : ℝ) := hVD.trans hpower
  refine ⟨D₁, hD₁, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnoncompact
  have hnonround := K.not_isRound_of_noncompact hnoncompact
  obtain ⟨N⟩ := P.normalization M K p 0 le_rfl
  have hR : 0 < (K.flow.connection 0).scalarCurvature p := N.scale_eq ▸ N.scale_pos
  have hscale : 0 ≤ (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ) :=
    Real.rpow_nonneg hR.le _
  obtain ⟨hvolLower, hvolUpper⟩ := hvolume K p hnonround
  refine ⟨?_, ?_, ?_⟩
  · intro x hx a b
    apply (le_abs_self _).trans_lt
    exact (hcurvature K p hnonround x hx a b).trans_le
      (mul_le_mul_of_nonneg_right hCD hR.le)
  · exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hlower hscale)).trans_lt hvolLower
  · exact hvolUpper.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hupper hscale))

theorem noncompact_uniform_core_upper_and_volume
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {D : ℝ} (hD : 1 < D) :
    ∃ D₁ : ℝ, 1 < D₁ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsCompact (Set.univ : Set M) →
        (∀ x ∈ (K.flow.metric 0).ball p
            (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ)),
          ∀ a b : TangentSpace (𝓡 3) x,
            (K.flow.connection 0).sectionalCurvature x a b <
              D₁ * (K.flow.connection 0).scalarCurvature p) ∧
        ENNReal.ofReal
            (D₁ ^ (-3 / 2 : ℝ) * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) <
          calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) ∧
        calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p
              (D * (K.flow.connection 0).scalarCurvature p ^ (-1 / 2 : ℝ))) <
          ENNReal.ofReal
            (D₁ ^ (3 / 2 : ℝ) * (K.flow.connection 0).scalarCurvature p ^ (-3 / 2 : ℝ)) := by
  exact noncompact_uniform_core_upper_and_volume_of_services P.noncompactServices hD

end PoincareConjecture
