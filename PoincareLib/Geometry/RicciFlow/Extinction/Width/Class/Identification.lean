import PoincareLib.Geometry.Riemannian.LoopSpace.Width

/-!
# M59 loop-class models and actual postcomposition

These primitive objects use the existing C1 loop topology and the actual cube
representatives of homotopy groups. One common cube-to-sphere quotient fixes
the parameter used by every normalized regular family. Relative squares have
three sides at a fixed constant loop and the fourth in the constant-loop
subspace, as in Perelman III, Section 1.

Source: Morgan--Tian Claim 18.16 and Definition 18.17, printed p. 430;
`references/derived/MT2007.txt:21046-21079` and
`references/derived/PerelmanIII.txt:34-40`. Smooth postcomposition carries the
whole loop extension; a merely Lipschitz map does not supply this C1 operation.
See `reviews/errata/2026-09-10-surgery-extinction-audit.md:68-85`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareMT

/-- A fixed cube-to-sphere parameter, collapsing exactly the cube boundary. -/
structure M59SphereQuotient where
  map : ContinuousMap (Fin 2 → I) LoopTwoSphere
  pole : LoopTwoSphere
  surjective : Function.Surjective map
  boundary_collapsed : ∀ y ∈ Cube.boundary (Fin 2), map y = pole
  exact_fibers : ∀ y z, map y = map z ↔
    y = z ∨ (y ∈ Cube.boundary (Fin 2) ∧ z ∈ Cube.boundary (Fin 2))

section Carrier

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The actual continuous sphere map displayed by a regular family. -/
def m59FamilyMap (Gamma : FreeTwoSphereFamily (M := M)) :
    ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)) :=
  ⟨Gamma.family, Gamma.continuous⟩

/-- Fix both the chosen point and the common sphere parameter. -/
def M59NormalizedAt (q : M59SphereQuotient) (x : M)
    (Gamma : FreeTwoSphereFamily (M := M)) : Prop :=
  Gamma.basepoint = x ∧ Gamma.class_certificate.sphere_parameter = q.map

/-- The pointed relative square for the pair of free loops and constant loops.
Three edges are fixed at `x`; the remaining edge consists of constant loops. -/
def M59RelativeLoopCubeAt (x : M)
    (F : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M))) : Prop :=
  (∀ z, z 0 = 0 ∨ z 1 = 0 ∨ z 1 = 1 → F z = constantC1Loop x) ∧
    ∀ z, z 0 = 1 → ∃ p : M, F z = constantC1Loop p

end Carrier

section Postcomposition

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

/-- Actual continuous postcomposition on the carried C1 loop extensions.
The existence conclusion takes smoothness of `f` as a separate primitive input. -/
structure M59LoopPostcomposition (f : ContinuousMap M N) where
  map : ContinuousMap (C1FreeLoopSpace (M := M)) (C1FreeLoopSpace (M := N))
  extension_agreement : ∀ gamma z, (map gamma).extension z = f (gamma.extension z)
  maps_constant : ∀ p : M, map (constantC1Loop p) = constantC1Loop (f p)

/-- The chosen point equality gives the corresponding based loop-map equality. -/
theorem M59LoopPostcomposition.map_based {f : ContinuousMap M N}
    (L : M59LoopPostcomposition f) {x : M} {y : N} (based : f x = y) :
    L.map (constantC1Loop x) = constantC1Loop y :=
  (L.maps_constant x).trans (congrArg constantC1Loop based)

end Postcomposition

end PoincareMT
