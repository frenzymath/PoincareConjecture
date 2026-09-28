import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.LimitMetricJets
import PoincareConjecture.Proofs.M34.Mathlib.AffineWithinJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (C : GeneralizedBlowupConvergence S J)

local instance : TopologicalSpace C.limit.carrier.carrier :=
  C.limit.carrier.topologicalSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier :=
  C.limit.carrier.isManifold

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem limitNoncollapse_generalized_uniform_spatialJetWithin
    (q : C.limit.sliceCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × E)) (hK : IsCompact K)
    (hdom : K ⊆ {z | z ∈ blowupMetricChartDomain C.limit q ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ C.exhaustion.space j})
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
      K ⊆ Icc (-C.exhaustion.time k) 0 ×ˢ
        (extChartAt (𝓡 3) q).target ∧
      ∀ a b : Fin 3, ∀ z ∈ K,
        ‖(iteratedFDerivWithin ℝ r
            (blowupPullbackCoefficient (C.embedding k) q a b)
            (Icc (-C.exhaustion.time k) 0 ×ˢ
              (extChartAt (𝓡 3) q).target) z).compContinuousLinearMap
              (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E) -
          (iteratedFDerivWithin ℝ r
            (FlowCarrier.coordinateCoefficient C.limit.carrier q
              (fun t x v w => (C.limit.flow.metric t).inner x v w) a b)
            (blowupMetricChartDomain C.limit q) z).compContinuousLinearMap
              (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E)‖ < epsilon := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ)
    (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E)
  obtain ⟨N, hjN, hN⟩ := C.pullback_metric_CInfinity q j r K hK hdom
    epsilon hepsilon
  refine ⟨N, hjN, fun k hk => ⟨(hN k hk).1, ?_⟩⟩
  intro a b z hz
  have hcomp := (hN k hk).2 a b z hz
  let Dk := iteratedFDerivWithin ℝ r
    (blowupPullbackCoefficient (C.embedding k) q a b)
    (Icc (-C.exhaustion.time k) 0 ×ˢ (extChartAt (𝓡 3) q).target) z
  let D0 := iteratedFDerivWithin ℝ r
    (FlowCarrier.coordinateCoefficient C.limit.carrier q
      (fun t x v w => (C.limit.flow.metric t).inner x v w) a b)
    (blowupMetricChartDomain C.limit q) z
  change ‖P (Dk - D0)‖ < epsilon
  exact ((Dk - D0).norm_compContinuous_linearIsometry_le
    (fun _ : Fin r => LinearIsometry.inr ℝ ℝ E)).trans_lt
    (by simpa only [Dk, D0] using hcomp)

end PoincareConjecture.M47
