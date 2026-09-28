import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47



theorem limitCanonical_finite_left_horizon_application
    {H : ℝ≥0∞} {V : GeneralizedBlowupSequence.{u}}
    (G : GeneralizedBlowupConvergence V (blowupBackwardInterval H))
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (k : ℕ) (s : ℝ)
    (hs : s ∈ Icc (-G.exhaustion.time k) 0) :
    ∃ ht : (V.base (G.subsequence k)).1 +
        s / V.scale (G.subsequence k) ∈
        (V.flow (G.subsequence k)).interval,
      let e := G.embedding k
      let chart := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
        (R (G.subsequence k)) s hs ht
      chart.source = G.exhaustion.space k ∧
        chart.target = limitRP2PhysicalMap e (R (G.subsequence k)) s hs ht ''
            G.exhaustion.space k ∧
        (∀ x ∈ G.exhaustion.space k, ∀ v w,
          (V.scale (G.subsequence k)) *
              ((F (G.subsequence k)).metric
                ((V.base (G.subsequence k)).1 +
                  s / V.scale (G.subsequence k))).inner
                (chart x)
                (mfderiv (𝓡 3) (𝓡 3) chart x v)
                (mfderiv (𝓡 3) (𝓡 3) chart x w) =
            e.pullbackInner s hs x v w) ∧
        (⟨(V.base (G.subsequence k)).1 +
            s / V.scale (G.subsequence k), chart G.limit.base⟩ :
            (t : ℝ) × ((F (G.subsequence k)).slice t).carrier) =
          ⟨(e.pointMap s hs G.limit.base).1,
            (R (G.subsequence k)).forward
              (e.pointMap s hs G.limit.base).1 ht
              (e.pointMap s hs G.limit.base).2⟩
  := by
  have ht := limitNoncollapse_physical_time_mem G k s hs
  refine ⟨ht, ?_⟩
  let e := G.embedding k
  let chart := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
    (R (G.subsequence k)) s hs ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact limitCanonicalPhysicalChart_source e (G.exhaustion.space_open k)
      (R (G.subsequence k)) s hs ht
  · exact limitCanonicalPhysicalChart_target e (G.exhaustion.space_open k)
      (R (G.subsequence k)) s hs ht
  · intro x hx v w
    exact limitCanonicalPhysicalChart_metric e (G.exhaustion.space_open k)
      (R (G.subsequence k)) s hs ht hx v w
  · exact limitCanonicalPhysicalChart_point_identity e
      (G.exhaustion.space_open k) (R (G.subsequence k)) s hs ht
      G.limit.base (e.pointMap s hs G.limit.base) ht rfl

end PoincareConjecture.M47
