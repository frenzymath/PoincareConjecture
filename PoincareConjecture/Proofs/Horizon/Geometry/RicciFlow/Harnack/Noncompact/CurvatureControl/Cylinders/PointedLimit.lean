import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

namespace PointedGeometricConvergence



theorem curvatureTensorNorm_base_pos_of_scalar_lower_bound
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hzero : 0 ∈ Ioo T' T)
    {c : ℝ} (hc : 0 < c)
    (hscalar : ∀ᶠ k in atTop,
      c ≤ ((S.flow k).flow.connection 0).scalarCurvature (S.flow k).base) :
    0 < (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base := by
  have hlimit := tendsto_const_nhds.mul (G.tendsto_curvatureTensorNorm 0 hzero
    G.limitFlow.base) (a := (n : ℝ) ^ 2)
  have hbound : c ≤ (n : ℝ) ^ 2 *
      (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base := by
    apply ge_of_tendsto hlimit
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hscalar] with k hk
    rw [congrArg Prod.snd (G.base_preserving k)]
    exact hk.trans ((le_abs_self _).trans
      (((S.flow (G.subsequence k)).flow.connection 0).abs_scalarCurvature_le_curvatureTensorNorm
        (S.flow (G.subsequence k)).base))
  by_contra! h
  have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (n : ℝ)) h
  linarith



theorem curvatureTensorNorm_le_of_uniform_ball_bound
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T) {K : ℝ}
    (hbound : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      ∀ t ∈ Ioo T' T, ∀ x ∈ (S.flow k).ballAt t A,
        ((S.flow k).flow.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Ioo T' T, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤ K := by
  let : PreconnectedSpace G.limitCarrier.carrier :=
    ⟨G.limitCarrier.connected.isPreconnected⟩
  intro t ht x
  let g := G.limitFlow.metricAt t
  let A := (g.edist G.limitFlow.base x).toReal + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hx : x ∈ G.limitFlow.ballAt t A := by
    change g.edist G.limitFlow.base x < ENNReal.ofReal A
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top G.limitFlow.base x)]
    exact ENNReal.ofReal_lt_ofReal_iff hA |>.mpr (by dsimp only [A]; linarith)
  apply le_of_tendsto (G.tendsto_curvatureTensorNorm t ht x)
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually
    (hbound (2 * A) (by positivity)), G.eventually_mem_ballAt hT ht hx] with k hk hxk
  exact hk t ht _ hxk

end PointedGeometricConvergence

namespace RicciFlow



theorem exists_nonflat_pointed_limit_of_terminal_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{0} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) {a ν : ℝ} (ha : a ≤ -2)
    (hJ : ∀ k, Icc a 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc a 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc a 0, ∀ x : (C k).carrier,
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
      ∃ G : PointedGeometricConvergence
        (bufferedCylinderSequence C J F p a δ (by linarith) hJ),
        (∀ t ∈ Ioo (a + δ) δ,
          G.limitCarrier.metricComplete (G.limitFlow.metricAt t)) ∧
        0 < (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base ∧
        ∀ t ∈ Ioo (a + δ) δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤
            ((m + 1 : ℕ) : ℝ) ^ 2 * 4 := by
  obtain ⟨ε, hε, hεone, hbuffer⟩ := exists_terminal_scalar_positive_time_buffer hC hm
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδone : δ < 1 := by dsimp only [δ]; linarith
  have hatime : a + δ < 0 := by linarith
  let S := bufferedCylinderSequence C J F p a δ (by linarith) hJ
  obtain ⟨H, hHS⟩ := exists_pointedCompactnessHypotheses_of_terminal_cylinders
    hC hm C J F p (by linarith : a ≤ -1) hδ hδone.le hatime hJ hcomplete hoperator
    L hL hscalar hν hvolume
  obtain ⟨P⟩ := pointedRicciFlowCompactness H hC
  have hlimit : ∃ G : PointedGeometricConvergence S,
      ∀ t ∈ Ioo (a + δ) δ,
        G.limitCarrier.metricComplete (G.limitFlow.metricAt t) := by
    rcases H with ⟨hT, seq, hvol, hcompact, hspace, hall, hnoncollapse⟩
    dsimp only at hHS
    subst seq
    exact ⟨P.geometric_limit, P.complete_interior⟩
  obtain ⟨G, hGcomplete⟩ := hlimit
  refine ⟨δ, hδ, hδone, G, hGcomplete, ?_, ?_⟩
  · apply G.curvatureTensorNorm_base_pos_of_scalar_lower_bound
      ⟨hatime, hδ⟩ (by norm_num : 0 < (1 : ℝ) / 2)
    filter_upwards [hL.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hk
    have hsub : Icc (-2 : ℝ) 0 ⊆ Icc a 0 := Icc_subset_Icc ha le_rfl
    have h := hbuffer (C k).carrier (J k) (F k)
      (fun _ ht => hJ k (hsub ht)) (fun t ht => hcomplete k t (hsub ht))
      (fun t ht => hoperator k t (hsub ht)) (p k)
      (fun t ht x hx => hscalar k t (hsub ht) x
        (hx.trans_le (ENNReal.ofReal_le_ofReal hk))) (hnormalize k)
      (-δ) ⟨by dsimp only [δ]; linarith, by linarith⟩
    dsimp only [S, bufferedCylinderSequence, RicciFlow.translate]
    change (1 : ℝ) / 2 ≤ ((F k).connection (0 + -δ)).scalarCurvature (p k)
    rw [zero_add]
    exact h
  · apply G.curvatureTensorNorm_le_of_uniform_ball_bound ⟨hatime, hδ⟩
    intro A _
    filter_upwards [hL.eventually_ge_atTop A] with k hk
    intro t ht x hx
    have hshift : t - δ ∈ Icc a 0 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (F k).curvatureTensorNorm_le_on_two_time_ball_of_terminal_cylinder hC
      (hJ k) (hoperator k) (p k) (hscalar k) hshift hshift hk x hx

end RicciFlow

end PoincareConjecture
