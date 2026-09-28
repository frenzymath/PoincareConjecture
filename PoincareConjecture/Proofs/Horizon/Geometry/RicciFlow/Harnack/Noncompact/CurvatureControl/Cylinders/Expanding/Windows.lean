import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.CurvatureLimit












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



theorem exists_common_buffer_pointed_limits_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{0} (m + 1)) (J : ℕ → Set ℝ)
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
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) 1)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ a : ℝ, ∀ ha : a ≤ -2,
      ∃ N : ℕ, ∃ hJN : ∀ k, Icc a 0 ⊆ interior (J (k + N)),
      ∃ G : PointedGeometricConvergence
        (bufferedCylinderSequence (fun k => C (k + N)) (fun k => J (k + N))
          (fun k => F (k + N)) (fun k => p (k + N)) a δ (by linarith) hJN),
        (∀ t ∈ Ioo (a + δ) δ,
          G.limitCarrier.metricComplete (G.limitFlow.metricAt t)) ∧
        (1 : ℝ) / 2 ≤ ((m + 1 : ℕ) : ℝ) ^ 2 *
          (G.limitFlow.flow.connection 0).curvatureTensorNorm G.limitFlow.base ∧
        (∀ t ∈ Ioo (a + δ) δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.flow.connection t).curvatureTensorNorm x ≤
            ((m + 1 : ℕ) : ℝ) ^ 2 * 4) ∧
        (∀ t ∈ Ioo (a + δ) δ, ∀ x : G.limitCarrier.carrier,
          (G.limitFlow.flow.connection t).NonnegativeCurvatureOperator x) := by
  obtain ⟨ε, hε, hεone, hbuffer⟩ := exists_terminal_scalar_positive_time_buffer hC hm
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδone : δ < 1 := by dsimp only [δ]; linarith
  refine ⟨δ, hδ, hδone, ?_⟩
  intro a ha
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hA.eventually_ge_atTop (-a))
  have hsub (k : ℕ) : Icc a 0 ⊆ Icc (-A (k + N)) 0 :=
    Icc_subset_Icc (by linarith [hN (k + N) (Nat.le_add_left N k)]) le_rfl
  have hJN : ∀ k, Icc a 0 ⊆ interior (J (k + N)) :=
    fun k _ ht => hJ (k + N) (hsub k ht)
  have hshift {t : ℝ} (ht : t ∈ Ioo (a + δ) δ) : t - δ ∈ Icc a 0 :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htail : Tendsto (fun k : ℕ => k + N) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  have hLN : Tendsto (fun k => L (k + N)) atTop atTop := hL.comp htail
  let S := bufferedCylinderSequence (fun k => C (k + N)) (fun k => J (k + N))
    (fun k => F (k + N)) (fun k => p (k + N)) a δ (by linarith) hJN
  obtain ⟨H, hHS⟩ := exists_pointedCompactnessHypotheses_of_terminal_cylinders
    hC hm (fun k => C (k + N)) (fun k => J (k + N))
    (fun k => F (k + N)) (fun k => p (k + N)) (by linarith : a ≤ -1)
    hδ hδone.le (by linarith) hJN
    (fun k t ht => hcomplete (k + N) t (hsub k ht))
    (fun k t ht x => hoperator (k + N) t (hsub k ht) x)
    (fun k => L (k + N)) hLN
    (fun k t ht x hx => hscalar (k + N) t (hsub k ht) x hx)
    hν (htail.eventually hvolume)
  obtain ⟨P⟩ := pointedRicciFlowCompactness H hC
  have hlimit : ∃ G : PointedGeometricConvergence S,
      ∀ t ∈ Ioo (a + δ) δ,
        G.limitCarrier.metricComplete (G.limitFlow.metricAt t) := by
    rcases H with ⟨hT, seq, hvol, hcompact, hspace, hall, hnoncollapse⟩
    dsimp only at hHS
    subst seq
    exact ⟨P.geometric_limit, P.complete_interior⟩
  obtain ⟨G, hGcomplete⟩ := hlimit
  refine ⟨N, hJN, G, hGcomplete, ?_, ?_, ?_⟩
  · apply G.scalar_lower_bound_le_mul_base_curvatureTensorNorm ⟨by linarith, hδ⟩
    filter_upwards [hLN.eventually_ge_atTop (64 * (((m + 1 : ℕ) : ℝ) + 8))] with k hk
    have htwo : Icc (-2 : ℝ) 0 ⊆ Icc a 0 := Icc_subset_Icc ha le_rfl
    have hb := hbuffer (C (k + N)).carrier (J (k + N)) (F (k + N))
      (fun _ ht => hJN k (htwo ht))
      (fun t ht => hcomplete (k + N) t (hsub k (htwo ht)))
      (fun t ht => hoperator (k + N) t (hsub k (htwo ht))) (p (k + N))
      (fun t ht x hx => hscalar (k + N) t (hsub k (htwo ht)) x
        (hx.trans_le (ENNReal.ofReal_le_ofReal hk))) (hnormalize (k + N))
      (-δ) ⟨by dsimp only [δ]; linarith, by linarith⟩
    change (1 : ℝ) / 2 ≤ ((F (k + N)).connection (0 + -δ)).scalarCurvature (p (k + N))
    rw [zero_add]
    exact hb
  · apply G.curvatureTensorNorm_le_of_uniform_ball_bound ⟨by linarith, hδ⟩
    intro R _
    filter_upwards [hLN.eventually_ge_atTop R] with k hk
    intro t ht x hx
    exact (F (k + N)).curvatureTensorNorm_le_on_two_time_ball_of_terminal_cylinder hC
      (hJN k) (fun s hs => hoperator (k + N) s (hsub k hs)) (p (k + N))
      (fun s hs => hscalar (k + N) s (hsub k hs)) (hshift ht) (hshift ht) hk x hx
  · exact nonnegativeCurvatureOperator_of_bufferedCylinderSequence
      (fun k => C (k + N)) (fun k => J (k + N)) (fun k => F (k + N))
      (fun k => p (k + N)) a δ (by linarith) hJN
      (fun k t ht => hoperator (k + N) t (hsub k ht)) G

end PoincareConjecture.RicciFlow
