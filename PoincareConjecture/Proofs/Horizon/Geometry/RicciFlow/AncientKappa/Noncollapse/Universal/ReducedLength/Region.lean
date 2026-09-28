import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ReducedLength.ShortPath










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M22UniversalNoncollapsingPredecessors

variable {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

include H



theorem reducedLength_two_le_on_ball (K : AncientKappaSolution 3 M) (p z : M)
    (hseed : reducedLength K.flow 0 p z 1 ≤ 3)
    (hscalar : ∀ x ∈ (K.flow.metric (-1)).ball z 1,
      (K.flow.connection (-1)).scalarCurvature x ≤ 2) :
    ∀ y ∈ (K.flow.metric (-1)).ball z (1 / 2),
      reducedLength K.flow 0 p y 2 ≤ universalNoncollapseLength := by
  have hwindow : Icc (0 - (3 : ℝ)) 0 ⊆ Iic (0 : ℝ) := fun _ ht => ht.2
  obtain ⟨L⟩ := H.ordinary_windows.m08 M (Iic 0) K.flow 0 3
    (by simp) (by norm_num) hwindow (H.complete_bounded_on K hwindow)
  intro y hy
  obtain ⟨W, hW, hIW, q, hq, hqone, hqtwo, hqscalar, hspeed⟩ :=
    H.exists_short_terminal_path K z y hy hscalar
  exact L.reducedLength_two_le_of_terminal_path (by norm_num) (by simp)
    (fun s hs => show 0 - s ≤ 0 by linarith [hs.1])
    (H.scalar_regular 3 M (Iic 0) K.flow).continuousOn
    p z y hseed q hW hIW hq hqone hqtwo hqscalar hspeed

end PoincareConjecture.M22UniversalNoncollapsingPredecessors
