import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.SmallLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

theorem exists_nonflat_ancient_limit_of_small_expanding_cylinders_quantitative_lt
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < η ∧
      ∃ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
        (fun k t => (F k).shrink.metric (t - δ))
        (fun k => equivShrink (C k).carrier (p k)) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (1 / 2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 *
          (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
        (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) := by
  obtain ⟨ε, hε, hεone, hbuffer⟩ := exists_terminal_scalar_positive_time_buffer hC hm
  let δ := min ε η / 2
  have hδ : 0 < δ := div_pos (lt_min hε hη) (by norm_num)
  have hδε : δ < ε := by
    have := min_le_left ε η
    dsimp [δ]
    linarith
  have hδη : δ < η := by
    have := min_le_right ε η
    dsimp [δ]
    linarith
  have hδone : δ < 1 := hδε.trans hεone
  have hsource : ∀ᶠ k in atTop,
      (1 : ℝ) / 2 ≤ ((F k).connection (-δ)).scalarCurvature (p k) := by
    filter_upwards [hA.eventually_ge_atTop 2,
      hL.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hkA hkL
    have hsub : Icc (-2 : ℝ) 0 ⊆ Icc (-A k) 0 :=
      Icc_subset_Icc (by linarith) le_rfl
    exact hbuffer (C k).carrier (J k) (F k) (fun _ ht => hJ k (hsub ht))
      (fun t ht => hcomplete k t (hsub ht)) (fun t ht => hoperator k t (hsub ht)) (p k)
      (fun t ht x hx => hscalar k t (hsub ht) x
        (hx.trans_le (ENNReal.ofReal_le_ofReal hkL))) (hnormalize k)
      (-δ) ⟨by linarith, by linarith⟩
  obtain ⟨G, hzero⟩ := exists_complete_ancient_limit_of_small_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hν hvolume hδ hδone
  obtain ⟨hGcomplete, hGnorm, hGoperator⟩ :=
    ancient_limit_properties_of_small_expanding_cylinders
      hC C J F p A L hA hL hJ hoperator hscalar hδ G hzero
  have hsmallbuffer : ∀ᶠ k in atTop,
      (1 : ℝ) / 2 ≤ (((F k).shrink.bufferedExpandingFlow δ).connection 0).scalarCurvature
        (equivShrink (C k).carrier (p k)) := by
    filter_upwards [hsource] with k hk
    change (1 : ℝ) / 2 ≤ ((F k).shrink.connection (0 - δ)).scalarCurvature _
    rw [shrink_scalarCurvature, Equiv.symm_apply_apply, zero_sub]
    exact hk
  have hquant := AncientPointedGeometricConvergence.scalar_lower_bound_le_mul_base_curvatureTensorNorm
    (C := fun k => (C k).shrink)
    (fun k => (F k).shrink.bufferedExpandingFlow δ) G hδ
    (eventually_buffered_time_window J A hA hJ δ) hsmallbuffer
  refine ⟨δ, hδ, hδone, hδη, G, hGcomplete, hquant, ?_, hGnorm, hGoperator⟩
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg (((m + 1 : ℕ) : ℝ))) (le_of_not_gt h)
  linarith

theorem exists_nonflat_ancient_limit_of_small_expanding_cylinders_lt
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    {ν : ℝ} (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < η ∧
      ∃ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
        (fun k t => (F k).shrink.metric (t - δ))
        (fun k => equivShrink (C k).carrier (p k)) δ,
        (∀ t ∈ Iio δ, G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
        (0 < (G.limitFlow.connection 0).curvatureTensorNorm G.base ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
         (∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.connection t).NonnegativeCurvatureOperator x)) := by
  obtain ⟨δ, hδ, hδone, hδη, G, hcompleteG, _, hnonflat, hboundG, hoperatorG⟩ :=
    exists_nonflat_ancient_limit_of_small_expanding_cylinders_quantitative_lt
      hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hnormalize hν hvolume hη
  exact ⟨δ, hδ, hδone, hδη, G, hcompleteG, hnonflat, hboundG, hoperatorG⟩

end PoincareConjecture.RicciFlow
