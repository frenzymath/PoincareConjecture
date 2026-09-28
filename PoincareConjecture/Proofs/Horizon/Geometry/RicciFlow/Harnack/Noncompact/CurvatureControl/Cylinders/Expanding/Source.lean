import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.Windows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

def bufferedExpandingFlow {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (δ : ℝ) :
    RicciFlow n M ((fun t : ℝ => t - δ) ⁻¹' J) :=
  F.translate (-δ) (by
    rintro _ ⟨t, ht, rfl⟩
    exact ht)
    ⟨fun x hx y hy z hz => F.interval.out hx hy ⟨by linarith [hz.1], by linarith [hz.2]⟩⟩
    (by
      obtain ⟨x, hx, y, hy, hxy⟩ := F.nontrivial
      refine ⟨x + δ, ?_, y + δ, ?_, ?_⟩
      · simpa using hx
      · simpa using hy
      · exact fun h => hxy (add_right_cancel h))

@[simp] theorem bufferedExpandingFlow_metric {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (δ t : ℝ) :
    (F.bufferedExpandingFlow δ).metric t = F.metric (t - δ) := rfl

@[simp] theorem bufferedExpandingFlow_connection {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (δ t : ℝ) :
    (F.bufferedExpandingFlow δ).connection t = F.connection (t - δ) := rfl

theorem eventually_buffered_time_window
    (J : ℕ → Set ℝ) (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k)) (δ a b : ℝ) (hb : b < δ) :
    ∀ᶠ k in atTop, Icc a b ⊆ (fun t : ℝ => t - δ) ⁻¹' J k := by
  filter_upwards [hA.eventually_ge_atTop (δ - a)] with k hk t ht
  change t - δ ∈ J k
  exact interior_subset (hJ k ⟨by linarith [ht.1], by linarith [ht.2]⟩)

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem exists_scalar_buffer_of_expanding_cylinders
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
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ k in atTop,
      (1 : ℝ) / 2 ≤ (((F k).bufferedExpandingFlow δ).connection 0).scalarCurvature (p k) := by
  obtain ⟨ε, hε, hεone, hbuffer⟩ := exists_terminal_scalar_positive_time_buffer hC hm
  refine ⟨ε / 2, by positivity, by linarith, ?_⟩
  filter_upwards [hA.eventually_ge_atTop 2,
    hL.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hkA hkL
  have hsub : Icc (-2 : ℝ) 0 ⊆ Icc (-A k) 0 :=
    Icc_subset_Icc (by linarith) le_rfl
  change (1 : ℝ) / 2 ≤ ((F k).connection (0 + -(ε / 2))).scalarCurvature (p k)
  rw [zero_add]
  exact hbuffer (C k).carrier (J k) (F k) (fun _ ht => hJ k (hsub ht))
    (fun t ht => hcomplete k t (hsub ht)) (fun t ht => hoperator k t (hsub ht)) (p k)
    (fun t ht x hx => hscalar k t (hsub ht) x
      (hx.trans_le (ENNReal.ofReal_le_ofReal hkL))) (hnormalize k)
    (-(ε / 2)) ⟨by linarith, by linarith⟩

end PoincareConjecture.RicciFlow
