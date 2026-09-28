import PoincareConjecture.Statements.M33BranchContinuation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.MaximalRestart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.RestartPinching
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.Conclusion
















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem M33Predecessors.exists_pinched_restart
    (P : M33Predecessors.{u}) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (a : ℝ) (ha : 0 ≤ a) (hpinched : HamiltonIveyPinchedAt D a) :
    ∃ b : ℝ≥0∞, ENNReal.ofReal a < b ∧
      ∃ F : RicciFlow 3 M {t : ℝ | a ≤ t ∧ ENNReal.ofReal t < b},
        F.metric a = g ∧
        (∀ t ∈ {s : ℝ | a ≤ s ∧ ENNReal.ofReal s < b},
          HamiltonIveyPinchedAt (F.connection t) t) ∧
        (∀ c : ℝ, a < c → ∀ G : RicciFlow 3 M (Set.Ico a c),
          G.metric a = g → ENNReal.ofReal c ≤ b) ∧
        (b ≠ ⊤ → ∀ C s : ℝ, s < b.toReal →
          ∃ t ∈ Set.Ioo (max a s) b.toReal, ∃ x : M,
            C < (F.connection t).curvatureTensorNorm x) := by
  obtain ⟨A⟩ := Surgery.OrdinaryRestart.nonempty_solution P.local_flow g
  refine ⟨ENNReal.ofReal a + Surgery.OrdinaryRestart.lifetime g,
    Surgery.OrdinaryRestart.absolute_lifetime_gt A a,
    Surgery.OrdinaryRestart.absoluteFlow P.local_flow.2.1 A a ha,
    Surgery.OrdinaryRestart.absoluteFlow_initial P.local_flow.2.1 A a ha, ?_,
    ?_, Surgery.OrdinaryRestart.absolute_curvature_unbounded_tail P.local_flow A a ha⟩
  · exact Surgery.OrdinaryRestart.absoluteFlow_pinched P.local_flow.2.1 A a ha
      (fun b hab F => P.pinching a b ha hab F)
      (Surgery.OrdinaryRestart.absoluteFlow_initial_pinched P.local_flow.2.1 A a ha D hpinched)
  · intro c hac G hG
    exact Surgery.OrdinaryRestart.absolute_time_le_lifetime ha hac G hG


theorem M33Predecessors.regular_history (P : M33Predecessors.{u})
    (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F) :
    Nonempty (M33RegularHistoryData W) := by
  refine ⟨Surgery.RegularHistory.data W (fun t _ ht => ?_)⟩
  let : CompactSpace (F.slice t).carrier :=
    isCompact_univ_iff.mp (F.slices_compact t (W.time_subset ht))
  exact P.local_flow

end PoincareConjecture
