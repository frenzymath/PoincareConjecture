import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic

/-!
# M53 repaired surgery-sphere separation statement

For a compact connected smooth three-manifold, every smoothly embedded
null-homotopic two-sphere has a disconnected complement.  The sphere and its
two primitive properties are represented directly in the input record; no
surgery event or endpoint classification is assumed at this node.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-!
Natural-language theorem: in a compact connected smooth three-manifold, every
smoothly embedded null-homotopic two-sphere separates the manifold.  The
statement is deliberately expressed using the primitive sphere object and its
smooth-embedding and null-homotopy properties; the later surgery adapter will
identify actual neck central spheres with this input.

Source: blueprint node `lem:nullhomotopic-embedded-sphere-separates`
(`5eda97c9d2c0`), formalized from the mod-2 Poincare-duality argument in
`foundations-and-interfaces.tex`, lines 463--483.  Morgan--Tian Proposition
15.12 and Remark 15.13 (printed p. 365) use this separation bridge for surgery
comparison.  The correction record is
`reviews/errata/2026-09-10-analytic-outline-audit.md`.
-/
structure RepairedSphereSeparationTheory : Prop where
  separation :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [CompactSpace M]
      [ConnectedSpace M],
      Nonempty (RepairedSphereSeparationData (M := M))

end PoincareMT
