import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpTangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

theorem seedLimit_physical_chart_tangent_norm
    {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
    {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval) {x : C.carrier} (hx : x ∈ U)
    (v : TangentSpace (𝓡 3) x) :
    (F.metric (origin + s / scale)).tangentNorm
        (limitCanonicalPhysicalChart e hU R s hs ht x)
        (mfderiv (𝓡 3) (𝓡 3) (limitCanonicalPhysicalChart e hU R s hs ht) x v) =
      (G.metric (origin + s / scale)).tangentNorm (e.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) := by
  have heq := limitCanonicalPhysicalChart_metric e hU R s hs ht hx v v
  dsimp only [GeneralizedFlowCylinder.pullbackInner] at heq
  exact congrArg Real.sqrt (mul_left_cancel₀ e.scale_pos.ne' heq)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem seedLimit_eventually_physical_tangent_comparison
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K)
    (t : ℝ) (ht : t ∈ J) {lambda : ℝ}
    (hlambda : 0 < lambda) (hlambda_lt : lambda < 1) :
    ∀ᶠ k in atTop,
      K ⊆ G.exhaustion.space k ∧ t ∈ Icc (-G.exhaustion.time k) 0 ∧
      ∀ hs : t ∈ Icc (-G.exhaustion.time k) 0,
        ∀ ht' : (V.base (G.subsequence k)).1 + t / V.scale (G.subsequence k) ∈
            (V.flow (G.subsequence k)).interval,
          let chart := limitCanonicalPhysicalChart (G.embedding k)
            (G.exhaustion.space_open k) (R (G.subsequence k)) t hs ht'
          ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
            (G.limit.flow.metric t).tangentNorm x v ≤
                (Real.sqrt (V.scale (G.subsequence k)) / lambda) *
                  ((F (G.subsequence k)).metric
                    ((V.base (G.subsequence k)).1 + t / V.scale (G.subsequence k))).tangentNorm
                    (chart x) (mfderiv (𝓡 3) (𝓡 3) chart x v) ∧
              ((F (G.subsequence k)).metric
                ((V.base (G.subsequence k)).1 + t / V.scale (G.subsequence k))).tangentNorm
                (chart x) (mfderiv (𝓡 3) (𝓡 3) chart x v) ≤
                  (1 / (lambda * Real.sqrt (V.scale (G.subsequence k)))) *
                    (G.limit.flow.metric t).tangentNorm x v := by
  filter_upwards [limitNoncollapse_generalized_compact_tangent_comparison
    G hK t ht hlambda hlambda_lt] with k hk
  refine ⟨hk.1, hk.2.1, ?_⟩
  intro hs ht' chart x hx v
  dsimp only [chart]
  rw [seedLimit_physical_chart_tangent_norm (G.embedding k)
    (G.exhaustion.space_open k) (R (G.subsequence k)) t hs ht' (hk.1 hx) v]
  exact hk.2.2 x hx v hs

end PoincareConjecture.Proofs.M47
