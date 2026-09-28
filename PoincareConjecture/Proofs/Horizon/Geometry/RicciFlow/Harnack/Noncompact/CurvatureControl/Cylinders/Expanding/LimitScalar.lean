import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.ScalarTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.SmallProperties









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

theorem exists_buffered_limit_scalar_normalization_constant
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
    (hbase : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ((F k).connection t).scalarCurvature (p k) ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
        (fun k t => (F k).shrink.metric (t - δ))
        (fun k => equivShrink (C k).carrier (p k)) δ,
        1 - D * δ ≤ (G.limitFlow.connection 0).scalarCurvature G.base ∧
          (G.limitFlow.connection 0).scalarCurvature G.base ≤ 1 := by
  obtain ⟨D, hD, hbound⟩ := eventually_terminal_scalar_control_of_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδone G
  have hconv : Tendsto (fun k : ℕ =>
      ((F (G.subsequence k)).connection (-δ)).scalarCurvature (p (G.subsequence k)))
      atTop (𝓝 ((G.limitFlow.connection 0).scalarCurvature G.base)) := by
    have h := AncientPointedGeometricConvergence.tendsto_scalarCurvature_at_zero_base
      (C := fun k => (C k).shrink)
      (fun k => (F k).shrink.bufferedExpandingFlow δ) G hδ
      (eventually_buffered_time_window J A hA hJ δ)
    apply h.congr'
    filter_upwards [] with k
    change ((F (G.subsequence k)).shrink.connection (0 - δ)).scalarCurvature
      (equivShrink (C (G.subsequence k)).carrier (p (G.subsequence k))) = _
    rw [shrink_scalarCurvature, Equiv.symm_apply_apply, zero_sub]
  constructor
  · apply ge_of_tendsto hconv
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hbound] with k hk
    have h := hk (-δ) ⟨by linarith, by linarith⟩
    rw [hnormalize] at h
    linarith
  · apply le_of_tendsto hconv
    filter_upwards [(hA.comp G.subsequence_strictMono.tendsto_atTop).eventually_ge_atTop 1]
      with k hk
    change 1 ≤ A (G.subsequence k) at hk
    exact hbase (G.subsequence k) (-δ) ⟨by linarith, by linarith⟩




theorem exists_buffered_limit_scalar_normalization_constant_universal
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
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
        (hbase : ∀ k, ∀ t ∈ Icc (-A k) 0,
          ((F k).connection t).scalarCurvature (p k) ≤ 1)
        {δ : ℝ}, 0 < δ → δ ≤ 1 →
        ∀ G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
          (fun k t => (F k).shrink.metric (t - δ))
          (fun k => equivShrink (C k).carrier (p k)) δ,
          1 - D * δ ≤ (G.limitFlow.connection 0).scalarCurvature G.base ∧
            (G.limitFlow.connection 0).scalarCurvature G.base ≤ 1 := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_terminal_scalar_control_of_expanding_cylinders_universal hC hm
  refine ⟨D, hD, ?_⟩
  intro C J F p A L hA hL hJ hcomplete hoperator hscalar hnormalize hbase
    δ hδ hδone G
  have hconv : Tendsto (fun k : ℕ =>
      ((F (G.subsequence k)).connection (-δ)).scalarCurvature (p (G.subsequence k)))
      atTop (𝓝 ((G.limitFlow.connection 0).scalarCurvature G.base)) := by
    have h := AncientPointedGeometricConvergence.tendsto_scalarCurvature_at_zero_base
      (C := fun k => (C k).shrink)
      (fun k => (F k).shrink.bufferedExpandingFlow δ) G hδ
      (eventually_buffered_time_window J A hA hJ δ)
    apply h.congr'
    filter_upwards [] with k
    change ((F (G.subsequence k)).shrink.connection (0 - δ)).scalarCurvature
      (equivShrink (C (G.subsequence k)).carrier (p (G.subsequence k))) = _
    rw [shrink_scalarCurvature, Equiv.symm_apply_apply, zero_sub]
  have hsource : ∀ᶠ k in atTop, ∀ t ∈ Icc (-1 : ℝ) 0,
      ((F k).connection 0).scalarCurvature (p k) -
          ((F k).connection t).scalarCurvature (p k) ≤ D * (0 - t) :=
    hbound C J F p A L hA hL hJ hcomplete hoperator hscalar
  constructor
  · apply ge_of_tendsto hconv
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hsource] with k hk
    have h := hk (-δ) ⟨by linarith, by linarith⟩
    rw [hnormalize] at h
    linarith
  · apply le_of_tendsto hconv
    filter_upwards [(hA.comp G.subsequence_strictMono.tendsto_atTop).eventually_ge_atTop 1]
      with k hk
    change 1 ≤ A (G.subsequence k) at hk
    exact hbase (G.subsequence k) (-δ) ⟨by linarith, by linarith⟩

end PoincareConjecture.RicciFlow
