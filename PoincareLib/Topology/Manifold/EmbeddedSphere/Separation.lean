import PoincareLib.Topology.Manifold.EmbeddedSphere.Theory
import PoincareLib.Topology.Manifold.EmbeddedSphere.Complement
import PoincareLib.Topology.Manifold.EmbeddedSphere.Separation.LocalParity

/-!
# M53 surgery-sphere separation proof entry

Natural-language theorem: in a compact connected smooth three-manifold, every
smoothly embedded null-homotopic two-sphere separates the manifold.  This is
the generic topological bridge later instantiated for actual surgery spheres.

Source: blueprint node `lem:nullhomotopic-embedded-sphere-separates`
(`5eda97c9d2c0`), formalized from the mod-2 Poincare-duality argument in
`foundations-and-interfaces.tex`, lines 463--483.  Morgan--Tian Proposition
15.12 and Remark 15.13 (printed p. 365) use this separation bridge for surgery
comparison.  The correction record is
`reviews/errata/2026-09-10-analytic-outline-audit.md`.

The entry combines the nonempty complement with the local parity
contradiction. The detailed argument and source correspondence are recorded
in `proof-work/tasks/M53/derivations/15-separation-assembly.md`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- A null-homotopic smoothly embedded sphere separates, including in a
nonorientable ambient manifold. This is the separation bridge used in
Morgan--Tian Proposition 15.12 and Remark 15.13, printed p. 365; see the
complete parity derivation in `derivations/15-separation-assembly.md`. -/
theorem repairedSphereSeparation : RepairedSphereSeparationTheory.{u} := by
  refine ⟨?_⟩
  intro M _ _ _ _ _ _ _
  refine ⟨⟨?_⟩⟩
  intro S
  refine ⟨Topology.EmbeddedSphere.sphere_complement_nonempty S, ?_⟩
  intro hconn
  apply Topology.EmbeddedSphere.sphere_complement_not_isPreconnected S
  simpa only [Set.compl_eq_univ_sdiff] using hconn.isPreconnected

end PoincareMT
