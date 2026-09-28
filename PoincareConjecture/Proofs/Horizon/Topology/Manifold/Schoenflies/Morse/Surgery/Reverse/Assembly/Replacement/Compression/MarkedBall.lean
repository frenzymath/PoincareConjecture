import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.MarkedBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Compression.Slab








set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_marked_ball_compression_away_disk
    (b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → S2) (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (W O : Set E3) (hW : IsOpen W) (hO : IsOpen O)
    (hDW : (fun x => b (g x)) '' closedBall (0 : E2) 1 ⊆ W)
    (hBO : (b '' closedBall (0 : E3) 1) \
      ((fun x => b (g x)) '' closedBall (0 : E2) 1) ⊆ O) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => b (g x)) '' closedBall (0 : E2) 1) ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x ∉ K, F x = x) ∧
        F '' (b '' closedBall (0 : E3) 1) ⊆
          (b '' closedBall (0 : E3) 1) ∩ W := by
  obtain ⟨C, e, hslab, _, _, hzero, hedge⟩ :=
    exists_marked_ball_sweep b g hgi hgl
  obtain ⟨_, _, _, _, K, hK, hKO, hKD, F, hfix, himage, _⟩ :=
    exists_slab_compression_away_disk_with_graph C e
      ((isCompact_closedBall 0 1).image b.continuous) hW hO hslab hzero
      (hedge.trans (image_mono sphere_subset_closedBall)) hDW hBO
  exact ⟨K, hK, hKO, hKD, F, hfix, himage⟩

end Poincare.Manifold.Schoenflies.Rounding
