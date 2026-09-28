import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.Lower.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Normalization.Carrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Nonround
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Transport











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace



theorem normalized_uniform_soul_core_sectional_lower_any_carrier_of_services
    (P : NoncompactKappaServices.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0)),
        ¬ IsCompact (univ : Set M) →
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature soul.center = 1 →
        ∀ x ∈ (K.flow.metric 0).ball soul.center D,
        ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
          c < (K.flow.connection 0).sectionalCurvature x v w := by
  obtain ⟨c, hc, hbound⟩ := normalized_uniform_soul_core_sectional_lower_of_services
    P htrichotomy hkappa hD
  refine ⟨c, hc, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K soul hnoncompact hnoncollapsed hnormalized x hx v w hvw
  let : NoncompactSpace M := ⟨hnoncompact⟩
  let B := K.toSmallBased soul.center hkappa hnoncollapsed hnormalized
  let e := Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M
  have hnc : NoncompactSpace B.carrier.carrier :=
    e.toHomeomorph.isClosedEmbedding.noncompactSpace
  let soul' := K.pointSoulToSmallBased soul.center hkappa hnoncollapsed hnormalized soul
  have hcenter : soul'.center = B.base := rfl
  have hx' : e x ∈ (B.flow.flow.metric 0).ball B.base D := by
    change (K.flow.shrink.metric 0).edist (equivShrink M soul.center) (equivShrink M x) < _
    rw [RicciFlow.shrink_edist, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact hx
  have hind : LinearIndependent ℝ
      ![mfderiv (𝓡 3) (𝓡 3) e x v, mfderiv (𝓡 3) (𝓡 3) e x w] := by
    let de := e.mfderivToContinuousLinearEquiv (by simp) x
    convert! hvw.map' de.toLinearMap (LinearMap.ker_eq_bot.mpr de.injective) using 1
    funext i
    fin_cases i <;> rfl
  have h := hbound B hnc ⟨soul', hcenter⟩ (e x) hx'
    (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) hind
  have hsec := Homothety.homothety_sectionalCurvature_eq
    (K.flow.metric 0) (B.flow.flow.metric 0) e 1 zero_lt_one
    (K.flow.metricHomothety_shrink 0) (K.flow.connection 0) (B.flow.flow.connection 0) x v w
  simpa only [div_one] using h.trans_eq hsec

theorem normalized_uniform_soul_core_sectional_lower_any_carrier
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {kappa D : ℝ} (hkappa : 0 < kappa) (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0)),
        ¬ IsCompact (univ : Set M) →
        AncientKappaNoncollapsed K.flow kappa →
        (K.flow.connection 0).scalarCurvature soul.center = 1 →
        ∀ x ∈ (K.flow.metric 0).ball soul.center D,
        ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
          c < (K.flow.connection 0).sectionalCurvature x v w := by
  exact normalized_uniform_soul_core_sectional_lower_any_carrier_of_services P.noncompactServices htrichotomy hkappa hD



theorem noncompact_uniform_soul_core_sectional_lower_multiple_of_services
    (P : NoncompactKappaServices.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {D : ℝ} (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0)),
        ¬ IsCompact (univ : Set M) →
        ∀ x ∈ (K.flow.metric 0).ball soul.center
          (D * (K.flow.connection 0).scalarCurvature soul.center ^ (-1 / 2 : ℝ)),
        ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
          c * (K.flow.connection 0).scalarCurvature soul.center <
            (K.flow.connection 0).sectionalCurvature x v w := by
  obtain ⟨kappa, hkappa, hnoncollapsed⟩ := P.universal_noncollapsing
  obtain ⟨c, hc, hbound⟩ := normalized_uniform_soul_core_sectional_lower_any_carrier_of_services
    P htrichotomy hkappa hD
  refine ⟨c, hc, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K soul hnoncompact x hx v w hvw
  let L : AncientKappaSolution 3 M := {
    K with
    kappa := kappa
    kappa_pos := hkappa
    noncollapsed := hnoncollapsed K (K.not_isRound_of_noncompact hnoncompact)
  }
  obtain ⟨A⟩ := P.normalization M L soul.center 0 le_rfl
  have hscale : A.scale = (K.flow.connection 0).scalarCurvature soul.center := A.scale_eq
  have hR : 0 < (K.flow.connection 0).scalarCurvature soul.center := hscale ▸ A.scale_pos
  have htarget : AncientKappaNoncollapsed A.target.flow kappa := by
    have hk : A.target.kappa = kappa := A.target_kappa
    rw [← hk]
    exact A.target.noncollapsed
  let soul' := A.pointSoul soul
  have hnormalized : (A.target.flow.connection 0).scalarCurvature soul'.center = 1 :=
    A.normalized_scalar
  have hx' : x ∈ (A.target.flow.metric 0).ball soul'.center D := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      ((A.target.flow.metric 0).edist_ne_top soul'.center x)).mpr
    rw [show soul'.center = soul.center from rfl, A.toReal_edist_zero, hscale]
    have hsqrt : 0 < Real.sqrt ((K.flow.connection 0).scalarCurvature soul.center) :=
      Real.sqrt_pos.mpr hR
    have hpower : (K.flow.connection 0).scalarCurvature soul.center ^ (-1 / 2 : ℝ) =
        (Real.sqrt ((K.flow.connection 0).scalarCurvature soul.center))⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
        Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow]
    have hxreal := (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top soul.center x)).mp hx
    rw [hpower] at hxreal
    change Real.sqrt ((K.flow.connection 0).scalarCurvature soul.center) *
      ((K.flow.metric 0).edist soul.center x).toReal < D
    calc
      _ < Real.sqrt ((K.flow.connection 0).scalarCurvature soul.center) *
          (D * (Real.sqrt ((K.flow.connection 0).scalarCurvature soul.center))⁻¹) :=
        mul_lt_mul_of_pos_left hxreal hsqrt
      _ = D := by field_simp
  have h := hbound A.target soul' hnoncompact htarget hnormalized x hx' v w hvw
  have hmetric : MetricHomothety (L.flow.metric 0) (A.target.flow.metric 0)
      (Diffeomorph.refl (𝓡 3) M ∞) A.scale := by
    intro z a b
    simpa [Diffeomorph.coe_refl, mfderiv_id] using A.metric_eq 0 z a b
  have hsec := Homothety.homothety_sectionalCurvature_eq
    (L.flow.metric 0) (A.target.flow.metric 0) (Diffeomorph.refl (𝓡 3) M ∞)
    A.scale A.scale_pos hmetric (L.flow.connection 0) (A.target.flow.connection 0) x v w
  have hsec' : (A.target.flow.connection 0).sectionalCurvature x v w =
      (L.flow.connection 0).sectionalCurvature x v w / A.scale := by
    simpa [Diffeomorph.coe_refl, mfderiv_id] using hsec
  simpa only [L, hscale] using (lt_div_iff₀ A.scale_pos).mp (h.trans_eq hsec')

theorem noncompact_uniform_soul_core_sectional_lower_multiple
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {D : ℝ} (hD : 0 < D) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0)),
        ¬ IsCompact (univ : Set M) →
        ∀ x ∈ (K.flow.metric 0).ball soul.center
          (D * (K.flow.connection 0).scalarCurvature soul.center ^ (-1 / 2 : ℝ)),
        ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
          c * (K.flow.connection 0).scalarCurvature soul.center <
            (K.flow.connection 0).sectionalCurvature x v w := by
  exact noncompact_uniform_soul_core_sectional_lower_multiple_of_services P.noncompactServices htrichotomy hD



theorem noncompact_uniform_soul_core_sectional_lower_of_services
    (P : NoncompactKappaServices.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {D : ℝ} (hD : 1 < D) :
    ∃ D₁ : ℝ, 1 < D₁ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0)),
        ¬ IsCompact (univ : Set M) →
        ∀ x ∈ (K.flow.metric 0).ball soul.center
          (D * (K.flow.connection 0).scalarCurvature soul.center ^ (-1 / 2 : ℝ)),
        ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
          D₁⁻¹ * (K.flow.connection 0).scalarCurvature soul.center <
            (K.flow.connection 0).sectionalCurvature x v w := by
  obtain ⟨c, hc, hbound⟩ := noncompact_uniform_soul_core_sectional_lower_multiple_of_services
    P htrichotomy (zero_lt_one.trans hD)
  let D₁ := 2 + c⁻¹
  have hD₁ : 1 < D₁ := by
    have := inv_pos.mpr hc
    dsimp [D₁]
    linarith
  have hlower : D₁⁻¹ ≤ c := inv_le_of_inv_le₀ hc (by dsimp [D₁]; linarith)
  refine ⟨D₁, hD₁, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K soul hnoncompact x hx v w hvw
  obtain ⟨A⟩ := P.normalization M K soul.center 0 le_rfl
  have hR : 0 < (K.flow.connection 0).scalarCurvature soul.center := A.scale_eq ▸ A.scale_pos
  exact (mul_le_mul_of_nonneg_right hlower hR.le).trans_lt
    (hbound K soul hnoncompact x hx v w hvw)

theorem noncompact_uniform_soul_core_sectional_lower
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (htrichotomy : CoreNormalizedCurvatureTrichotomy)
    {D : ℝ} (hD : 1 < D) :
    ∃ D₁ : ℝ, 1 < D₁ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M)
        (soul : RiemannianMetric.PointSoulData (K.flow.metric 0)),
        ¬ IsCompact (univ : Set M) →
        ∀ x ∈ (K.flow.metric 0).ball soul.center
          (D * (K.flow.connection 0).scalarCurvature soul.center ^ (-1 / 2 : ℝ)),
        ∀ v w : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![v, w] →
          D₁⁻¹ * (K.flow.connection 0).scalarCurvature soul.center <
            (K.flow.connection 0).sectionalCurvature x v w := by
  exact noncompact_uniform_soul_core_sectional_lower_of_services P.noncompactServices htrichotomy hD

end PoincareConjecture
