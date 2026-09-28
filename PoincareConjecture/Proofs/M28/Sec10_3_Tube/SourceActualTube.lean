import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceActualChain
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFiniteCertificate










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28




theorem exists_actual_source_tube_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
          ∃ (L : SourceOrientedList S) (B : BalancedNeckChain (E.flow.metric E.time) epsilon),
            B.shape = ChainShape.finite 0 (L.nodes.length - 1) ∧
            B.neck = neckOfList (L.nodes.map Prod.snd) (L.nodes.head L.nonempty).2 ∧
            B.source_necks = S.cover.necks ∧
            ∃ T : EpsilonTubeCertificate (E.flow.metric E.time) S.cover.X,
              T.epsilon = epsilon ∧ HEq T.chain B ∧ T.carrier = B.unionOpen := by
  obtain ⟨epsilonC, hCpos, hCsmall, hC⟩ := exists_actual_source_balanced_chain_accuracy.{u}
  obtain ⟨epsilonT, hTpos, _, hT⟩ :=
    BalancedNeckChain.exists_finite_tubeCertificate_threshold_m28.{u}
  refine ⟨min epsilonC epsilonT, lt_min hCpos hTpos,
    (min_le_left _ _).trans hCsmall, ?_⟩
  intro epsilon C A D₀ D E S hbase hsmall
  obtain ⟨L, B, hshape, hneck, hsource, hcover⟩ :=
    hC E S hbase (hsmall.trans (min_le_left _ _))
  obtain ⟨T, heps, hchain, hcarrier⟩ := hT B
    (hsmall.trans (min_le_right _ _)) 0 (L.nodes.length - 1) hshape S.cover.X hcover
  exact ⟨L, B, hshape, hneck, hsource, T, heps, hchain, hcarrier⟩

end PoincareConjecture.M28
