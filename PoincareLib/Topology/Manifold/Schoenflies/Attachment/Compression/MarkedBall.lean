import PoincareLib.Topology.Manifold.Schoenflies.Attachment.Rounding.Chart.MarkedBall
import PoincareLib.Topology.Manifold.Schoenflies.Attachment.Compression.Slab

/-!
# Supported compression of a marked ball

Compress an ambient ball into any neighborhood of a regular marked closed
boundary disk, fixing a neighborhood of that disk and controlling the support.

Reference: Hatcher, Notes on Basic 3-Manifold Topology (2014), Theorem 1.1,
reverse-surgery induction, printed pp. 4-5, and Lemma 1.3, printed p. 5.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

/-- Compress the entire marked ball with compact support away from its marked
closed disk, inside any prescribed neighborhood of the original ball. -/
theorem exists_marked_ball_compression
    (b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → S2) (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (W O : Set E3) (hW : IsOpen W) (hO : IsOpen O)
    (hDW : (fun x => b (g x)) '' closedBall (0 : E2) 1 ⊆ W)
    (hBO : b '' closedBall (0 : E3) 1 ⊆ O) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => b (g x)) '' closedBall (0 : E2) 1) ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x ∉ K, F x = x) ∧
        F '' (b '' closedBall (0 : E3) 1) ⊆
          (b '' closedBall (0 : E3) 1) ∩ W := by
  obtain ⟨C, e, hslab, _, _, hzero, hedge⟩ :=
    exists_marked_ball_sweep b g hgi hgl
  exact exists_slab_compression C e ((isCompact_closedBall 0 1).image b.continuous)
    hW hO hslab hzero (hedge.trans (image_mono sphere_subset_closedBall)) hDW hBO

end Poincare.Manifold.Schoenflies.Rounding
