import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BoundedSide
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Assembly
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Tree
import Mathlib.Geometry.Manifold.Instances.Sphere

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.SmoothDomain
open _root_.PoincareConjecture

namespace M38Schoenflies

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.SmoothDomain

theorem exists_ball_neighborhood
    {Omega : Set (EuclideanSpace Real (Fin 3))}
    (D : Poincare.Manifold.SmoothDomain 3 Omega)
    (f : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ->
      EuclideanSpace Real (Fin 3))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hfront : Set.range f = frontier Omega) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace Real (Fin 3))
        (EuclideanSpace Real (Fin 3)),
      Metric.closedBall 0 1 ⊆ e.source ∧
      closure Omega ⊆ e.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e '' Metric.closedBall 0 1 = closure Omega := by
  exact Schoenflies.SaddleLevel.OrientationReview.exists_ball_neighborhood D f hf hfront

end Poincare.Manifold.SmoothDomain

end M38Schoenflies
