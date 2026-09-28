import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareConjecture

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

def m59FamilyMap (Gamma : FreeTwoSphereFamily (M := M)) :
    ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)) :=
  ⟨Gamma.family, Gamma.continuous⟩

def M59NormalizedAt (q : M59SphereQuotient) (x : M)
    (Gamma : FreeTwoSphereFamily (M := M)) : Prop :=
  Gamma.basepoint = x ∧ Gamma.class_certificate.sphere_parameter = q.map

def M59RelativeLoopCubeAt (x : M)
    (F : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M))) : Prop :=
  (∀ z, z 0 = 0 ∨ z 1 = 0 ∨ z 1 = 1 → F z = constantC1Loop x) ∧
    ∀ z, z 0 = 1 → ∃ p : M, F z = constantC1Loop p

end Carrier

section Postcomposition

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

structure M59LoopPostcomposition (f : ContinuousMap M N) where
  map : ContinuousMap (C1FreeLoopSpace (M := M)) (C1FreeLoopSpace (M := N))
  extension_agreement : ∀ gamma z, (map gamma).extension z = f (gamma.extension z)
  maps_constant : ∀ p : M, map (constantC1Loop p) = constantC1Loop (f p)

theorem M59LoopPostcomposition.map_based {f : ContinuousMap M N}
    (L : M59LoopPostcomposition f) {x : M} {y : N} (based : f x = y) :
    L.map (constantC1Loop x) = constantC1Loop y :=
  (L.maps_constant x).trans (congrArg constantC1Loop based)

end Postcomposition

end PoincareConjecture
