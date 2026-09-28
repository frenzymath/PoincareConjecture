import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Confinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.RadiusLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem terminal_ball_volume_le_enlarged
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a b S r : ℝ} (hm : 0 < m) (hab : a ≤ b)
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hS : 0 ≤ S)
    (hscalar : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).scalarCurvature x ≤ S)
    (p : M) (hr : 0 < r) :
    ((F.metric b).volumeMeasure ((F.metric b).ball p r)).toReal ≤
      ((F.metric a).volumeMeasure
        ((F.metric a).ball p (r + (4 * ((m + 1 : ℕ) : ℝ) + 8 * S) * (b - a) + 1))).toReal := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hD (t : ℝ) : (F.connection t).CurvatureTensorCalculus :=
    hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t)
  have hRic (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (v : TangentSpace (𝓡 (m + 1)) x) : 0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hD t) x (hoperator t ht x) v).1
  have hupper (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (v : TangentSpace (𝓡 (m + 1)) x) :
      (F.connection t).ricci x v v ≤ S * (F.metric t).inner x v v := by
    have hv : 0 ≤ (F.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric t).pos x v hv).le
    exact ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hD t) x (hoperator t ht x) v).2.trans
        (mul_le_mul_of_nonneg_right (hscalar t ht x) hv)
  have hsub : (F.metric b).ball p r ⊆
      (F.metric a).ball p (r + (4 * ((m + 1 : ℕ) : ℝ) + 8 * S) * (b - a) + 1) := by
    intro x hx
    have h := F.terminal_closedBall_distance_bound hC hm hab hJ hcomplete hRic p hS
      (by norm_num : 0 < (1 : ℝ)) hr.le
      (fun t ht x _ v => hupper t ht x v)
      (r := r + (4 * ((m + 1 : ℕ) : ℝ) + 8 * S) * (b - a) + 1)
      (by simp only [mul_one, div_one]; linarith) a ha x
      (show (F.metric b).edist p x ≤ ENNReal.ofReal r from hx.le)
    exact h.2
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m + 1)))
      (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
    ⟨⟨(F.metric b).inner, (F.metric b).toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
  have hmeas : MeasurableSet ((F.metric b).ball p r) :=
    (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
  have hfixed := F.antitoneOn_volumeMeasure_of_scalarCurvature_nonneg hJ
    (fun t _ => hD t) hmeas
    ((F.metric b).isCompact_closure_ball_of_metricComplete (hcomplete b hb) p r)
    subset_closure (fun t ht x _ => Finset.sum_nonneg (fun i _ => hRic t ht x _))
    ha hb hab
  exact hfixed.trans (ENNReal.toReal_mono
    ((F.metric a).ball_volume_ne_top_of_metricComplete (hcomplete a ha) p _)
    (measure_mono hsub))

end PoincareConjecture.RicciFlow
