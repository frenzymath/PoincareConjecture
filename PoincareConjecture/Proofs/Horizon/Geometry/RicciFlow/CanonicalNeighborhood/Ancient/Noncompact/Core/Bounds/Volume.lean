import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.NormalizedScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.UniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.MaximalBalls











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

open RiemannianMetric



theorem noncompact_core_fixed_kappa_unit_volume_lower_of_services
    (P : NoncompactKappaServices.{u})
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p 1) := by
  obtain ⟨C, hC, hscalar⟩ := noncompact_uniform_scalar_bound_of_normalized P hkappa
    (show (0 : ℝ) < 1 by norm_num)
  let r : ℝ := (C + 1)⁻¹
  have hr : 0 < r := inv_pos.mpr (by linarith)
  have hr1 : r ≤ 1 := (inv_le_one₀ (by linarith : 0 < C + 1)).mpr (by linarith)
  have hCr : C ≤ r⁻¹ ^ 2 := by
    dsimp [r]
    rw [inv_inv]
    nlinarith [sq_nonneg C]
  have hv : 0 < kappa * r ^ 3 := mul_pos hkappa (pow_pos hr 3)
  refine ⟨kappa * r ^ 3 / 2, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnc hnormalized
  have hsmall : ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r) := by
    apply hnc r hr 0 le_rfl p r hr le_rfl
    intro t ht q hq
    rw [abs_of_nonneg (show 0 ≤ (K.flow.connection t).curvatureTensorNorm q from
      Real.sqrt_nonneg _)]
    apply (P.past_norm_le_scalar M K t 0 ht.2 le_rfl q).trans
    apply (hscalar K p hnc hnormalized q ?_).trans hCr
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal hr1)
  have hball : (K.flow.metric 0).ball p r ⊆ (K.flow.metric 0).ball p 1 := by
    intro q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal hr1)
  have hstrict : ENNReal.ofReal (kappa * r ^ 3 / 2) <
      ENNReal.ofReal (kappa * r ^ 3) :=
    (ENNReal.ofReal_lt_ofReal_iff hv).mpr (by linarith)
  exact hstrict.trans_le (hsmall.trans (MeasureTheory.measure_mono hball))

theorem noncompact_core_fixed_kappa_unit_volume_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p 1) := by
  exact noncompact_core_fixed_kappa_unit_volume_lower_of_services P.noncompactServices hkappa



theorem noncompact_core_fixed_kappa_normalized_volume_bounds_of_services
    (P : NoncompactKappaServices.{u})
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 1 < D) :
    ∃ v V : ℝ, 0 < v ∧ 0 < V ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p D) ∧
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p D) <
          ENNReal.ofReal V := by
  obtain ⟨v, hv, hlower⟩ := noncompact_core_fixed_kappa_unit_volume_lower_of_services P hkappa
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  have hmodel : 0 < euclideanUnitBallVolume 3 * D ^ 3 :=
    mul_pos (euclideanUnitBallVolume_pos 3) (pow_pos hDpos 3)
  refine ⟨v, euclideanUnitBallVolume 3 * D ^ 3 + 1, hv, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hnc hnormalized
  constructor
  · apply (hlower K p hnc hnormalized).trans_le
    apply MeasureTheory.measure_mono
    intro q hq
    exact lt_of_lt_of_le hq (ENNReal.ofReal_le_ofReal hD.le)
  · have hRic (x : M) (a : TangentSpace (𝓡 3) x) :
        0 ≤ (K.flow.connection 0).ricci x a a :=
      ((K.flow.connection 0).ricci_bounds_of_nonnegative_curvatureOperator
        (P.tensor_calculus 3 M (K.flow.metric 0) (K.flow.connection 0)) x
        (K.nonnegative_curvature_operator 0 le_rfl x) a).1
    have hupper := (K.flow.metric 0).ball_volume_div_pow_le_euclideanUnitBallVolume
      (K.flow.connection 0) (by norm_num) (K.complete 0 le_rfl) hRic p hDpos
    have hreal := (div_le_iff₀ (pow_pos hDpos 3)).mp hupper
    rw [calibratedMetricVolume_eq_volumeMeasure,
      ← ENNReal.ofReal_toReal ((K.flow.metric 0).ball_volume_ne_top_of_metricComplete
        (K.complete 0 le_rfl) p D)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by linarith :
      0 < euclideanUnitBallVolume 3 * D ^ 3 + 1)).mpr
    linarith

theorem noncompact_core_fixed_kappa_normalized_volume_bounds
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 1 < D) :
    ∃ v V : ℝ, 0 < v ∧ 0 < V ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p D) ∧
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p D) <
          ENNReal.ofReal V := by
  exact noncompact_core_fixed_kappa_normalized_volume_bounds_of_services P.noncompactServices hkappa hD



theorem noncompact_core_uniform_unit_volume_lower_of_services
    (P : NoncompactKappaServices.{u}) :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p 1) := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨v, hv, hbound⟩ := noncompact_core_fixed_kappa_unit_volume_lower_of_services P hkappa
  exact ⟨v, hv, fun K p hnonround hnormalized =>
    hbound K p (hnoncollapsed K hnonround) hnormalized⟩

theorem noncompact_core_uniform_unit_volume_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p 1) := by
  exact noncompact_core_uniform_unit_volume_lower_of_services P.noncompactServices



theorem noncompact_core_uniform_normalized_volume_bounds_of_services
    (P : NoncompactKappaServices.{u})
    {D : ℝ} (hD : 1 < D) :
    ∃ v V : ℝ, 0 < v ∧ 0 < V ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p D) ∧
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p D) <
          ENNReal.ofReal V := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨v, V, hv, hV, hbound⟩ :=
    noncompact_core_fixed_kappa_normalized_volume_bounds_of_services P hkappa hD
  exact ⟨v, V, hv, hV, fun K p hnonround hnormalized =>
    hbound K p (hnoncollapsed K hnonround) hnormalized⟩

theorem noncompact_core_uniform_normalized_volume_bounds
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    {D : ℝ} (hD : 1 < D) :
    ∃ v V : ℝ, 0 < v ∧ 0 < V ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) (p : M),
        ¬ IsRoundAncientKappaSolution K →
        (K.flow.connection 0).scalarCurvature p = 1 →
        ENNReal.ofReal v < calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball p D) ∧
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p D) <
          ENNReal.ofReal V := by
  exact noncompact_core_uniform_normalized_volume_bounds_of_services P.noncompactServices hD

end PoincareConjecture
