import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Inheritance
import PoincareLib.Geometry.RicciFlow.Compactness.Ancient.Scalar

/-!
# Scalar monotonicity on the retained raw ancient limit

Finite windows preserve the same carrier, flow, subsequence and spatial maps.
The existing scalar and curvature-norm convergence theorems therefore apply
at every fixed interior point. The original structural inequalities pass to
the raw limit before any globally bounded ancient-solution package is formed.

Reference: Morgan--Tian, Theorem 9.64, pp. 225-229; Kleiner--Lott,
Theorem 46.1, pp. 2687-2688.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

namespace AncientPointedGeometricConvergence

variable {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
  (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
  (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
  (hT : 0 < T)
  (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)

include hT htime

/-- Scalar curvature converges at every fixed interior point along the
original ancient subsequence and its time-independent spatial maps. -/
theorem tendsto_scalarCurvature_on_finite_windows
    (t : ℝ) (ht : t < T) (x : G.limitCarrier.carrier) :
    Tendsto (fun k => ((F (G.subsequence k)).connection t).scalarCurvature
      (G.embedding k x)) atTop
      (𝓝 ((G.limitFlow.connection t).scalarCurvature x)) := by
  obtain ⟨a, b, ha, hb, hbT, htw⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr ht)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply (tendsto_add_atTop_iff_nat N).mp
  exact W.tendsto_scalarCurvature t (htw (mem_singleton t)) x

/-- Curvature norms converge through the same spatial maps at every fixed
interior point of the one ancient limit. -/
theorem tendsto_curvatureTensorNorm_on_finite_windows
    (t : ℝ) (ht : t < T) (x : G.limitCarrier.carrier) :
    Tendsto (fun k => ((F (G.subsequence k)).connection t).curvatureTensorNorm
      (G.embedding k x)) atTop
      (𝓝 ((G.limitFlow.connection t).curvatureTensorNorm x)) := by
  obtain ⟨a, b, ha, hb, hbT, htw⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr ht)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply (tendsto_add_atTop_iff_nat N).mp
  exact W.tendsto_curvatureTensorNorm t (htw (mem_singleton t)) x

end AncientPointedGeometricConvergence

namespace NormalizedKappaSolutionSequence

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance monotonicitySourceConnected (k : ℕ) :
    ConnectedSpace (S.term k).carrier.carrier := (S.term k).connectedSpace

variable (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
  (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)

/-- Scalar convergence for the actual shifted normalized source sequence. -/
theorem interiorLimit_tendsto_scalarCurvature
    (t : ℝ) (ht : t < 1) (x : G.limitCarrier.carrier) :
    Tendsto (fun k => ((S.term (G.subsequence k)).flow.flow.connection (t - 1)).scalarCurvature
      (G.embedding k x)) atTop (𝓝 ((G.limitFlow.connection t).scalarCurvature x)) := by
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  apply G.tendsto_scalarCurvature_on_finite_windows F (by norm_num) ?_ t ht x
  intro a b hb
  exact Eventually.of_forall fun k s hs => by
    change s - 1 ≤ 0
    linarith [hs.2]

/-- Curvature-norm convergence for the same shifted source sequence. -/
theorem interiorLimit_tendsto_curvatureTensorNorm
    (t : ℝ) (ht : t < 1) (x : G.limitCarrier.carrier) :
    Tendsto (fun k => ((S.term (G.subsequence k)).flow.flow.connection (t - 1)).curvatureTensorNorm
      (G.embedding k x)) atTop (𝓝 ((G.limitFlow.connection t).curvatureTensorNorm x)) := by
  let F (k : ℕ) : RicciFlow 3 (S.term k).carrier.carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (S.term k).flow.flow.bufferedExpandingFlow 1
  apply G.tendsto_curvatureTensorNorm_on_finite_windows F (by norm_num) ?_ t ht x
  intro a b hb
  exact Eventually.of_forall fun k s hs => by
    change s - 1 ≤ 0
    linarith [hs.2]

/-- Scalar monotonicity passes from M16's actual source solutions to the
same raw limit without a global curvature bound on that limit. -/
theorem interiorLimit_scalar_monotone
    (P : M23NormalizedKappaCompactnessPredecessors)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 1) (x : G.limitCarrier.carrier) :
    (G.limitFlow.connection s).scalarCurvature x ≤
      (G.limitFlow.connection t).scalarCurvature x := by
  apply le_of_tendsto_of_tendsto
    (S.interiorLimit_tendsto_scalarCurvature G s (hst.trans_lt ht) x)
    (S.interiorLimit_tendsto_scalarCurvature G t ht x)
  exact Eventually.of_forall fun k => P.scalar_monotone
    (S.term (G.subsequence k)).carrier.carrier (S.term (G.subsequence k)).flow
    (s - 1) (t - 1) (by linarith) (by linarith) (G.embedding k x)

/-- The full-curvature bound by later scalar curvature also passes through
the same maps, before packaging the raw limit as an ancient kappa-solution. -/
theorem interiorLimit_past_norm_le_scalar
    (P : M23NormalizedKappaCompactnessPredecessors)
    {s t : ℝ} (hst : s ≤ t) (ht : t < 1) (x : G.limitCarrier.carrier) :
    |(G.limitFlow.connection s).curvatureTensorNorm x| ≤
      (G.limitFlow.connection t).scalarCurvature x := by
  rw [abs_of_nonneg (show 0 ≤ (G.limitFlow.connection s).curvatureTensorNorm x from
    Real.sqrt_nonneg _)]
  apply le_of_tendsto_of_tendsto
    (S.interiorLimit_tendsto_curvatureTensorNorm G s (hst.trans_lt ht) x)
    (S.interiorLimit_tendsto_scalarCurvature G t ht x)
  exact Eventually.of_forall fun k => P.past_norm_le_scalar
    (S.term (G.subsequence k)).carrier.carrier (S.term (G.subsequence k)).flow
    (s - 1) (t - 1) (by linarith) (by linarith) (G.embedding k x)

end NormalizedKappaSolutionSequence
end PoincareMT
