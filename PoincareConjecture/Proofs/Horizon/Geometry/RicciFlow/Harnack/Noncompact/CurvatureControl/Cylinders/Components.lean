import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.PointedLimit

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

noncomputable abbrev componentFlowCarrier
    {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (p : M) : FlowCarrier.{u} n where
  carrier := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance
  connected := isConnected_univ

abbrev componentFlowBase
    {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (p : M) : (componentFlowCarrier (n := n) p).carrier :=
  ⟨p, mem_connectedComponent⟩

theorem exists_pointedCompactnessHypotheses_of_terminal_cylinders_components
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (M : ℕ → Type) [∀ k, TopologicalSpace (M k)] [∀ k, MeasurableSpace (M k)]
    [∀ k, BorelSpace (M k)] [∀ k, T3Space (M k)] [∀ k, SecondCountableTopology (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (M k)]
    [∀ k, IsManifold (𝓡 (m + 1)) ∞ (M k)]
    (J : ℕ → Set ℝ) (F : ∀ k, RicciFlow (m + 1) (M k) (J k))
    (p : ∀ k, M k) {a δ ν : ℝ}
    (ha : a ≤ -1) (hδ : 0 < δ) (hδone : δ ≤ 1) (hatime : a + δ < 0)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc a 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc a 0, ∀ x : M k,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hscalar : ∀ k, ∀ t ∈ Icc a 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1)) :
    ∃ H : PointedRicciFlowCompactnessHypotheses (m + 1) (a + δ) δ,
      H.sequence = bufferedCylinderSequence
        (fun k => componentFlowCarrier (n := m + 1) (p k)) J
        (fun k => (F k).restrictComponent (p k))
        (fun k => componentFlowBase (n := m + 1) (p k))
        a δ (by linarith) hJ := by
  apply exists_pointedCompactnessHypotheses_of_terminal_cylinders (ν := ν) hC hm
    (fun k => componentFlowCarrier (n := m + 1) (p k)) J
    (fun k => (F k).restrictComponent (p k))
    (fun k => componentFlowBase (n := m + 1) (p k)) ha hδ hδone hatime hJ
    (fun k t ht => (F k).restrictComponent_metricComplete (p k) t (hcomplete k t ht))
    (fun k t ht x => ((F k).restrictComponent_nonnegativeCurvatureOperator_iff
      (p k) t x).mpr (hoperator k t ht x)) L hL
  · intro k t ht x hx
    rw [(F k).restrictComponent_scalarCurvature]
    apply hscalar k t ht x
    change (((F k).restrictComponent (p k)).metric 0).edist
      (componentFlowBase (n := m + 1) (p k)) x < ENNReal.ofReal (L k) at hx
    rwa [(F k).restrictComponent_edist] at hx
  · exact hν
  · filter_upwards [hvolume] with k hk
    rwa [(F k).restrictComponent_volumeMeasure_ball]

theorem exists_nonflat_pointed_limit_of_terminal_cylinders_components
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (M : ℕ → Type) [∀ k, TopologicalSpace (M k)] [∀ k, MeasurableSpace (M k)]
    [∀ k, BorelSpace (M k)] [∀ k, T3Space (M k)] [∀ k, SecondCountableTopology (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (M k)]
    [∀ k, IsManifold (𝓡 (m + 1)) ∞ (M k)]
    (J : ℕ → Set ℝ) (F : ∀ k, RicciFlow (m + 1) (M k) (J k))
    (p : ∀ k, M k) {a ν : ℝ} (ha : a ≤ -2)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc a 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc a 0, ∀ x : M k,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hscalar : ∀ k, ∀ t ∈ Icc a 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    (hnormalize : ∀ k, ((F k).connection 0).scalarCurvature (p k) = 1)
    (hν : 0 < ν)
    (hvolume : ∀ᶠ k in atTop, ENNReal.ofReal ν ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ G : PointedGeometricConvergence (bufferedCylinderSequence
        (fun k => componentFlowCarrier (n := m + 1) (p k)) J
        (fun k => (F k).restrictComponent (p k))
        (fun k => componentFlowBase (n := m + 1) (p k))
        a δ (by linarith) hJ),
        (∀ t ∈ Ioo (a + δ) δ,
          G.limitCarrier.metricComplete (G.limitFlow.metricAt t)) ∧
        (letI := G.limitCarrier.topologicalSpace
         letI := G.limitCarrier.chartedSpace
         letI := G.limitCarrier.isManifold
         0 < (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base ∧
         ∀ t ∈ Ioo (a + δ) δ, ∀ x : G.limitCarrier.carrier,
           (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤
             ((m + 1 : ℕ) : ℝ) ^ 2 * 4) := by
  apply exists_nonflat_pointed_limit_of_terminal_cylinders (ν := ν) hC hm
    (fun k => componentFlowCarrier (n := m + 1) (p k)) J
    (fun k => (F k).restrictComponent (p k))
    (fun k => componentFlowBase (n := m + 1) (p k)) ha hJ
    (fun k t ht => (F k).restrictComponent_metricComplete (p k) t (hcomplete k t ht))
    (fun k t ht x => ((F k).restrictComponent_nonnegativeCurvatureOperator_iff
      (p k) t x).mpr (hoperator k t ht x)) L hL
  · intro k t ht x hx
    rw [(F k).restrictComponent_scalarCurvature]
    apply hscalar k t ht x
    change (((F k).restrictComponent (p k)).metric 0).edist
      (componentFlowBase (n := m + 1) (p k)) x < ENNReal.ofReal (L k) at hx
    rwa [(F k).restrictComponent_edist] at hx
  · intro k
    rw [(F k).restrictComponent_scalarCurvature]
    exact hnormalize k
  · exact hν
  · filter_upwards [hvolume] with k hk
    rwa [(F k).restrictComponent_volumeMeasure_ball]

end PoincareConjecture.RicciFlow
