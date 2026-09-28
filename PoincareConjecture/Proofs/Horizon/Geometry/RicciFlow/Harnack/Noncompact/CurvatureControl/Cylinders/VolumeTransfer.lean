import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Confinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.RadiusLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem terminal_ball_volume_le_earlier_ball_of_cylinder
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a b S r ρ L : ℝ} (hm : 0 < m) (hab : a ≤ b)
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hS : 0 ≤ S) (p : M)
    (hscalar : ∀ t ∈ Icc a b, ∀ x ∈ (F.metric b).ball p L,
      (F.connection t).scalarCurvature x ≤ S)
    (hr : 0 < r)
    (hgap : r + (4 * ((m + 1 : ℕ) : ℝ) + 8 * S) * (b - a) < ρ)
    (hρ : ρ ≤ L) :
    (F.metric b).volumeMeasure ((F.metric b).ball p r) ≤
      (F.metric a).volumeMeasure ((F.metric a).ball p ρ) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hD (t : ℝ) : (F.connection t).CurvatureTensorCalculus :=
    hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t)
  have hRic (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (v : TangentSpace (𝓡 (m + 1)) x) : 0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hD t) x (hoperator t ht x) v).1
  have hupper (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (hx : x ∈ (F.metric t).ball p ρ) (v : TangentSpace (𝓡 (m + 1)) x) :
      (F.connection t).ricci x v v ≤ S * (F.metric t).inner x v v := by
    have hxterminal : x ∈ (F.metric b).ball p ρ :=
      F.ball_subset_ball_of_ricci_nonneg hJ p ρ ht hb ht.2
        (fun s hs y _ w => hRic s hs y w) hx
    have hxL : x ∈ (F.metric b).ball p L :=
      lt_of_lt_of_le hxterminal (ENNReal.ofReal_le_ofReal hρ)
    have hv : 0 ≤ (F.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric t).pos x v hv).le
    exact ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hD t) x (hoperator t ht x) v).2.trans
        (mul_le_mul_of_nonneg_right (hscalar t ht x hxL) hv)
  have hsub : (F.metric b).ball p r ⊆ (F.metric a).ball p ρ := by
    intro x hx
    have h := F.terminal_closedBall_distance_bound hC hm hab hJ hcomplete hRic p hS
      (by norm_num : 0 < (1 : ℝ)) hr.le hupper
      (by simpa only [mul_one, div_one] using hgap) a ha x
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
  apply (ENNReal.toReal_le_toReal
    ((F.metric b).ball_volume_ne_top_of_metricComplete (hcomplete b hb) p r)
    ((F.metric a).ball_volume_ne_top_of_metricComplete (hcomplete a ha) p ρ)).mp
  exact hfixed.trans (ENNReal.toReal_mono
    ((F.metric a).ball_volume_ne_top_of_metricComplete (hcomplete a ha) p ρ)
    (measure_mono hsub))

theorem terminal_unit_ball_volume_le_buffered_ball_of_cylinder
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    (hm : 0 < m) (hJ : Icc (-1 : ℝ) 0 ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc (-1 : ℝ) 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc (-1 : ℝ) 0, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (p : M)
    (hscalar : ∀ t ∈ Icc (-1 : ℝ) 0,
      ∀ x ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)),
        (F.connection t).scalarCurvature x ≤ 4)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 0) :
    (F.metric 0).volumeMeasure ((F.metric 0).ball p 1) ≤
      (F.metric t).volumeMeasure
        ((F.metric t).ball p (4 * ((m + 1 : ℕ) : ℝ) + 34)) := by
  have hsub : Icc t 0 ⊆ Icc (-1 : ℝ) 0 :=
    fun _ hs => ⟨ht.1.trans hs.1, hs.2⟩
  apply F.terminal_ball_volume_le_earlier_ball_of_cylinder hC hm ht.2
    (fun _ hs => hJ (hsub hs)) (fun s hs => hcomplete s (hsub hs))
    (fun s hs => hoperator s (hsub hs)) (by norm_num : 0 ≤ (4 : ℝ)) p
    (fun s hs => hscalar s (hsub hs)) (by norm_num : 0 < (1 : ℝ))
  · have hn : 0 ≤ ((m + 1 : ℕ) : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left (show 0 - t ≤ 1 by linarith [ht.1])
      (show 0 ≤ 4 * ((m + 1 : ℕ) : ℝ) + 8 * 4 by positivity)
    linarith
  · have hn : 0 ≤ ((m + 1 : ℕ) : ℝ) := by positivity
    linarith

end PoincareConjecture.RicciFlow
