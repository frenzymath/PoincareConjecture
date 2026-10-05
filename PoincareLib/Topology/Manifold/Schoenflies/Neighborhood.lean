import PoincareLib.Geometry.Manifold.SmoothDomain
import PoincareLib.Topology.Manifold.Schoenflies.CompactExtension
import PoincareLib.Topology.Manifold.Schoenflies.BoundedSide
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Assembly
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Tree
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smooth ball neighborhoods of sphere-bounded domains

The neighborhood form of the smooth three-dimensional Schoenflies theorem.
The hypotheses use the existing smooth structure on the actual domain
closure; they do not assume a ball parametrization.

Reference: Hatcher, Notes on Basic 3-Manifold Topology (2014), Section 1.1,
smooth-category convention and Theorem 1.1, printed p. 1, proof pp. 2-5.
The neighborhood form additionally needs extension across boundary collars.

The construction uses the four-model terminal saddle planar family and cap
replacement, including their height-reflected orientations.

The ambient construction can be stated independently of the domain argument:
for a smooth embedding `f` of the unit sphere, construct a global smooth
ambient diffeomorphism `F` of Euclidean three-space with `F p = f p` on the
sphere.  Its restriction to the closed ball is injective and locally smoothly
invertible, and therefore supplies the existential map below.  Hatcher's
smooth proof (Theorem 1.1, printed pp. 2-5) obtains this endpoint by putting
the sphere in Morse position, performing smooth planar disk surgeries, and
reversing the surgeries by ball attachment and isotopy extension.

Several operations in this route are now constructed without admissions:
`Isotopy.Extension` extends a prescribed smooth sphere isotopy to ambient
diffeomorphisms with one compact support, and `Attachment.Local` constructs
the supported push from a flat boundary to a smooth graph inside a supplied
boundary chart. The latter is the pushing ingredient of Hatcher's Lemma 1.3,
printed p. 5. `Isotopy.Linearization` constructs a supported isotopy to the
derivative on a small ball around a nonsingular point; `Isotopy.BallShrinking`
constructs radial contraction with support in any specified larger ball.
`Isotopy.BallEmbedding` combines compact isotopy extension with uniform local
linearization to extend every nonsingular embedding of a closed ball to a
global ambient diffeomorphism. This starts from an already filled ball.
`Isotopy.BallContraction` contracts an embedded disk by an ambient isotopy of
its manifold, and `Isotopy.BallStraightening` straightens a chart ball in a
chosen chart at its center. `Hemisphere` supplies central projection charts;
`LinearBall` extends normalized linear sphere maps across the entire ball.
`Attachment.MarkedBall` now assembles these operations: it constructs a
global ambient diffeomorphism preserving the closed ball and normalizing
any parametrized marked boundary disk to a round cap. The proof uses its
constructed sphere isotopy, not the general sphere-isotopy classification.
`Attachment.DiskComplement` constructs smooth neighborhood coordinates for
the complementary disk. `Morse.Coordinates` constructs a height with finitely
many critical points and signed-square coordinates at each one, directly
from the given embedding. `Morse.Perturbation.DistinctValues` separates their
heights by a constructed compactly supported ambient diffeomorphism while
preserving the critical set and Morse charts. `Morse.Caps` identifies the
local extremum disks, and `Morse.RegularLevel.Cuts` chooses finitely many regular
slicing levels with at most one critical point between them and finitely many
components in each slice. `Morse.RegularLevel.Band` constructs the normalized-gradient
transport across regular height bands. `Morse.RegularLevel.Circle` parametrizes every
regular component by the standard circle, using the proved compact
one-manifold classification; `Morse.RegularLevel.Projection` identifies its smooth planar
embedding. `Morse.RegularLevel.Flattening` constructs a compactly supported,
height-preserving ambient diffeomorphism straightening a regular annulus into
the cylinder over its central component. It uses `Isotopy.Circle`, the
ambient extension of a prescribed smooth family of embedded planar circles.
`Isotopy.RadialGraph` constructs ambient diffeomorphisms for positive radial
sphere graphs, including the explicit smooth capped-cylinder model in
`Morse.Models.RoundedCylinder`. `Morse.Models.CylindricalBody` identifies its
closed and open filled cylinders in a central slab. `Attachment.MarkedBallFlattening`
flattens an arbitrary filled marked ball and identifies its filled side;
`Attachment.Nesting` supplies the disjoint-or-nested alternative and finite
innermost-ball selection. `Morse.RegularLevel.Separation` identifies both
complementary regions of a regular circle in the sphere.
`Morse.Surgery.Iteration.MorseReduction` constructs a finite tree of actual
two-sided disk surgeries from the original embedding. Every inserted cap
survives unchanged in one terminal sphere, and every original critical point
survives with its embedding germ. Each terminal height band contains at most
one original critical point. `Morse.Surgery.Iteration.Core.Filling` constructs
ambient fillings for every regular, minimum, and maximum terminal core from
its actual path and preserved caps. The remaining terminal case has a unique
saddle with its exact interior Morse chart. `Morse.Surgery.Reverse.Tree`
propagates terminal fillings through the actual exact reverse attachments
and undoes the initial ambient Morse perturbation. The complete saddle
terminal filling combines `saddle_planar_family_leaf` with the proved
`saddle_cap_replacement_leaf`. Both four-model leaves and the assembly have
recursive audits restricted to the standard logical axioms.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.SmoothDomain

/-- A relatively compact smooth domain in Euclidean three-space bounded by a
smoothly embedded two-sphere is the image of the unit closed ball under a
diffeomorphism defined on an open neighborhood of that ball. -/
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
