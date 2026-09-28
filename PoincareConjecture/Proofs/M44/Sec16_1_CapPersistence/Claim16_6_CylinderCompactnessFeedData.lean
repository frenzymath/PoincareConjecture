import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderCoordinateEstimates
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CompactnessFeedJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => StandardCapSpace

noncomputable local instance cylinderFeedCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance cylinderFeedCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace




structure CylinderCompactnessSample (g0 : StandardInitialMetric)
    (F : SurgeryFlowData.{u}) (a : ℝ) (ha : a ∈ F.surgery_times)
    [Nonempty (F.slice a).carrier] (i : Fin (F.event a ha).cap_count) where

  standard_initial_eq : F.standard_initial = g0

  radius : ℝ

  radius_pos : 0 < radius

  eta : ℝ

  radius_lt : radius < eta⁻¹

  lifetime : ℝ

  lifetime_pos : 0 < lifetime

  comparison : SurgeryCapClose F.standard_initial
    ((F.event a ha).local_result i).output ((F.event a ha).local_result i).metric
    ((F.event a ha).local_result i).tip (((F.event a ha).necks i).neck.scale) eta

  image_ball : ∀ r : ℝ, 0 < r → r ≤ eta⁻¹ →
    comparison.map '' F.standard_initial.metric.ball 0 r =
      ((F.event a ha).local_result i).metric.ball ((F.event a ha).local_result i).tip
        (((F.event a ha).necks i).neck.scale * r)

  chart : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice a).carrier ∞

  chart_source : chart.source = F.standard_initial.metric.ball 0 radius

  chart_eq : ∀ y, chart y = (F.event a ha).local_embed i (comparison.map y)

  region : Set (F.slice a).carrier

  cylinder : SurgeryFlowCylinder F (F.slice a) a ((F.parameters.h a)⁻¹ ^ 2)
    (Ico 0 lifetime) region

  chart_target_subset : chart.target ⊆ region

  birth_identity : ∀ h y, y ∈ region → HEq (cylinder.forward 0 h y) y

  ordinary : CylinderRicciFlow cylinder chart

  target_point : (⟨chart.target, chart.open_target⟩ : Opens (F.slice a).carrier)

namespace CylinderCompactnessSample

variable {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
  {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
  {i : Fin (F.event a ha).cap_count}



noncomputable def coefficients (D : CylinderCompactnessSample g0 F a ha i) :
    ℝ × E → MetricCoefficient 3 := fun p =>
  (D.ordinary.flow.metric p.1).pullbackCoefficients (targetChart D.chart D.target_point) p.2



theorem source_eq (D : CylinderCompactnessSample g0 F a ha i) :
    D.chart.source = g0.metric.ball 0 D.radius := by
  rw [D.chart_source, D.standard_initial_eq]



theorem coefficients_smooth (D : CylinderCompactnessSample g0 F a ha i) :
    ContDiffOn ℝ ∞ D.coefficients (Ico 0 D.lifetime ×ˢ D.chart.source) :=
  contDiffOn_pullbackCoefficients_within D.ordinary.flow D.chart.open_source
    (contMDiffOn_targetChart D.chart D.target_point)



theorem target_derivative_invertible (D : CylinderCompactnessSample g0 F a ha i)
    {x : E} (hx : x ∈ D.chart.source) :
    (mfderiv (𝓡 3) (𝓡 3) (targetChart D.chart D.target_point) x).IsInvertible := by
  have h := (targetPartialDiffeomorph D.chart D.target_point).isLocalDiffeomorphAt
    (𝓡 3) (𝓡 3) ∞ hx
  exact ⟨h.mfderivToContinuousLinearEquiv (by simp), rfl⟩



theorem coefficients_invertible (D : CylinderCompactnessSample g0 F a ha i)
    (t : ℝ) {x : E} (hx : x ∈ D.chart.source) :
    (D.coefficients (t, x)).IsInvertible :=
  (D.ordinary.flow.metric t).isInvertible_pullbackCoefficients
    (D.target_derivative_invertible hx).injective



theorem coefficients_symmetric (D : CylinderCompactnessSample g0 F a ha i)
    (p : ℝ × E) (v w : E) : D.coefficients p v w = D.coefficients p w v :=
  (D.ordinary.flow.metric p.1).symm _ _ _



theorem coefficients_evolution (D : CylinderCompactnessSample g0 F a ha i)
    {t : ℝ} (ht : t ∈ Ioo 0 D.lifetime) {x : E} (hx : x ∈ D.chart.source) :
    HasDerivAt (fun s => D.coefficients (s, x))
      (ricciFlowOperator 3 (metricTwoJet (fun y => D.coefficients (t, y)) x)) t := by
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow D.ordinary.flow
    (show Ioo (0 : ℝ) D.lifetime ⊆ Ico 0 D.lifetime from Ioo_subset_Ico_self)
    ordConnected_Ioo (Ioo_infinite D.lifetime_pos).nontrivial
  exact hasDerivAt_pullbackCoefficients_ricci G isOpen_Ioo D.chart.open_source
    (contMDiffOn_targetChart D.chart D.target_point)
    (fun _ hy => D.target_derivative_invertible hy) ht hx




theorem initial_coefficients (D : CylinderCompactnessSample g0 F a ha i)
    {x : E} (hx : x ∈ D.chart.source) :
    D.coefficients (0, x) = D.comparison.normalizedCoefficients x := by
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  have hscale : 0 < (F.parameters.h a)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hh)
  let g := m01RescaledMetric (F.metric a) ((F.parameters.h a)⁻¹ ^ 2) hscale
  have hg (y) (v w) : g.inner y v w =
      (F.parameters.h a)⁻¹ ^ 2 * (F.metric a).inner y v w := rfl
  have hdomain : D.chart.source ⊆ F.standard_initial.metric.ball 0 D.eta⁻¹ := by
    rw [D.chart_source]
    exact fun _ hy => hy.trans_le (ENNReal.ofReal_le_ofReal D.radius_lt.le)
  exact (D.ordinary.initial_pullback_eq ⟨le_rfl, D.lifetime_pos⟩
    D.chart_target_subset D.birth_identity g hg D.target_point hx).trans
      (physical_birth_pullback_eq F a ha i D.comparison g hg D.chart.open_source hdomain
        (fun y _ => D.chart_eq y) hx)



theorem initial_spatial_jet (D : CylinderCompactnessSample g0 F a ha i)
    {x : E} (hx : x ∈ D.chart.source) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => D.coefficients (0, y)) x =
      iteratedFDeriv ℝ m D.comparison.normalizedCoefficients x := by
  have heq : (fun y => D.coefficients (0, y)) =ᶠ[𝓝 x]
      D.comparison.normalizedCoefficients :=
    eventually_of_mem (D.chart.open_source.mem_nhds hx) (fun _ hy => D.initial_coefficients hy)
  exact (heq.iteratedFDeriv ℝ m).eq_of_nhds



def fixedComparison (D : CylinderCompactnessSample g0 F a ha i) :
    SurgeryCapClose g0 ((F.event a ha).local_result i).output
      ((F.event a ha).local_result i).metric ((F.event a ha).local_result i).tip
      (((F.event a ha).necks i).neck.scale) D.eta :=
  Eq.mp (congrArg (fun g : StandardInitialMetric =>
    SurgeryCapClose g ((F.event a ha).local_result i).output
      ((F.event a ha).local_result i).metric ((F.event a ha).local_result i).tip
      (((F.event a ha).necks i).neck.scale) D.eta) D.standard_initial_eq) D.comparison

end CylinderCompactnessSample




theorem normalizedCoefficients_cast_initial
    {g0 g1 : StandardInitialMetric} (h : g0 = g1)
    {S : GeneralizedSliceCarrier.{u}} {g : RiemannianMetric 3 S.carrier}
    {tip : S.carrier} {scale eta : ℝ} (Q : SurgeryCapClose g0 S g tip scale eta) :
    (Eq.mp (congrArg (fun g' : StandardInitialMetric =>
      SurgeryCapClose g' S g tip scale eta) h) Q).normalizedCoefficients =
        Q.normalizedCoefficients := by
  subst g1
  rfl

end PoincareConjecture.M44
