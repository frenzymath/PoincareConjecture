import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Growth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem exists_potential_gradient_linear_growth_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (a b : ℝ) (hb : b < 0) (s : ℝ) (hs : s ∈ Icc a b) :
    ∃ A : ℝ, 0 < A ∧ ∀ t ∈ Icc a b,
      ∀ x : L.convergence.limit.carrier.carrier,
        (L.convergence.limit.flow.metric s).tangentNorm x
          ((L.convergence.limit.flow.connection t).gradient
            (fun y => L.potential (y, t)) x) ≤
          A * (1 + ((L.convergence.limit.flow.metric s).edist
            L.convergence.limit.base x).toReal) := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  let F := L.convergence.limit.flow
  let p := L.convergence.limit.base
  obtain ⟨C, hC0, hhess⟩ := L.exists_hessian_quadratic_bound_on_Icc hC hbound a b hb
  obtain ⟨G, hG, hbase⟩ := L.exists_potential_gradient_norm_bound_on_Icc p a b hb
  obtain ⟨B, hB, hcompare⟩ := L.exists_tangentNorm_comparison_on_Icc hC hbound a b hb
  let A₀ := B * (G + 1)
  let A₁ := B * (4 * C * B)
  have hA₀ : 0 ≤ A₀ := mul_nonneg hB.le (by linarith)
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  refine ⟨A₀ + A₁ + 1, by positivity, ?_⟩
  intro t ht x
  have ht0 : t < 0 := ht.2.trans_lt hb
  have hgrowth := (F.connection t).gradient_norm_le_base_add_of_hessian_bound
    (L.convergence.limit.complete t ht0) (L.contMDiff_potential_slice t ht0)
    hC0 (hhess t ht) p x
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) + 1 = 4 by norm_num] at hgrowth
  have hdist : (F.metric t).edist p x ≤ ENNReal.ofReal B * (F.metric s).edist p x := by
    simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using
      (F.metric s).edist_le_mul_of_tangentNorm_mfderiv_le (F.metric t)
        (F := id) contMDiff_id hB (fun y v => by
          simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using
            hcompare t ht s hs y v) p x
  have hdistR := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((F.metric s).edist_ne_top p x)) hdist
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB.le] at hdistR
  have hcurrent : (F.metric t).tangentNorm x
      ((F.connection t).gradient (fun y => L.potential (y, t)) x) ≤
      G + 1 + 4 * C * (B * ((F.metric s).edist p x).toReal) := by
    apply hgrowth.trans
    exact add_le_add (add_le_add (hbase t ht) le_rfl)
      (mul_le_mul_of_nonneg_left hdistR (by positivity))
  have href := (hcompare s hs t ht x _).trans
    (mul_le_mul_of_nonneg_left hcurrent hB.le)
  change (F.metric s).tangentNorm x
    ((F.connection t).gradient (fun y => L.potential (y, t)) x) ≤
      (A₀ + A₁ + 1) * (1 + ((F.metric s).edist p x).toReal)
  calc
    _ ≤ A₀ + A₁ * ((F.metric s).edist p x).toReal := by
      exact href.trans_eq (by dsimp [A₀, A₁]; ring)
    _ ≤ _ := by
      nlinarith [ENNReal.toReal_nonneg (a := (F.metric s).edist p x),
        mul_nonneg hA₀ (ENNReal.toReal_nonneg (a := (F.metric s).edist p x))]

theorem exists_negative_potential_gradient_linear_growth_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (a b : ℝ) (hb : b < 0) (s : ℝ) (hs : s ∈ Icc a b) :
    ∃ A : ℝ, 0 < A ∧ ∀ t ∈ Icc a b,
      ∀ x : L.convergence.limit.carrier.carrier,
        (L.convergence.limit.flow.metric s).tangentNorm x
          (-((L.convergence.limit.flow.connection t).gradient
            (fun y => L.potential (y, t)) x)) ≤
          A * (1 + ((L.convergence.limit.flow.metric s).edist
            L.convergence.limit.base x).toReal) := by
  obtain ⟨A, hA, hboundA⟩ := L.exists_potential_gradient_linear_growth_on_Icc
    hC hbound a b hb s hs
  refine ⟨A, hA, fun t ht x => ?_⟩
  simpa only [RiemannianMetric.tangentNorm, map_neg, neg_apply, neg_neg] using hboundA t ht x

end PoincareConjecture.AncientAsymptoticSolitonLimitData
