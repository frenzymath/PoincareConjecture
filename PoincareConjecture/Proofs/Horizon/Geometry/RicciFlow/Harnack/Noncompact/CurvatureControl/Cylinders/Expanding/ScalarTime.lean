import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.ScalarTime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Carrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal

universe u
namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.secondCountable

theorem eventually_terminal_scalar_control_of_expanding_cylinders
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
        ((F k).connection t).scalarCurvature x ≤ 4) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in atTop, ∀ t ∈ Icc (-1 : ℝ) 0,
      ((F k).connection 0).scalarCurvature (p k) -
        ((F k).connection t).scalarCurvature (p k) ≤ D * (0 - t) := by
  obtain ⟨D, hD, hbound⟩ := exists_terminal_scalar_time_constant hC hm
  refine ⟨D, hD, ?_⟩
  filter_upwards [hA.eventually_ge_atTop 2,
    hL.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hkA hkL
  have hsub : Icc (-2 : ℝ) 0 ⊆ Icc (-A k) 0 :=
    Icc_subset_Icc (by linarith) le_rfl
  exact hbound (C k).carrier (J k) (F k) (fun _ ht => hJ k (hsub ht))
    (fun t ht => hcomplete k t (hsub ht))
    (fun t ht => hoperator k t (hsub ht)) (p k)
    (fun t ht x hx => hscalar k t (hsub ht) x
      (hx.trans_le (ENNReal.ofReal_le_ofReal hkL)))

theorem exists_terminal_scalar_control_of_expanding_cylinders_universal
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
            ((F k).connection t).scalarCurvature x ≤ 4),
        ∀ᶠ k in atTop, ∀ t ∈ Icc (-1 : ℝ) 0,
          ((F k).connection 0).scalarCurvature (p k) -
            ((F k).connection t).scalarCurvature (p k) ≤ D * (0 - t) := by
  obtain ⟨D, hD, hbound⟩ := exists_terminal_scalar_time_constant hC hm
  refine ⟨D, hD, ?_⟩
  intro C J F p A L hA hL hJ hcomplete hoperator hscalar
  filter_upwards [hA.eventually_ge_atTop 2,
    hL.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hkA hkL
  have hsub : Icc (-2 : ℝ) 0 ⊆ Icc (-A k) 0 :=
    Icc_subset_Icc (by linarith) le_rfl
  exact hbound (C k).carrier (J k) (F k) (fun _ ht => hJ k (hsub ht))
    (fun t ht => hcomplete k t (hsub ht))
    (fun t ht => hoperator k t (hsub ht)) (p k)
    (fun t ht x hx => hscalar k t (hsub ht) x
      (hx.trans_le (ENNReal.ofReal_le_ofReal hkL)))

end PoincareConjecture.RicciFlow
