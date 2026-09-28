import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

structure EpsilonNeck.GraphicalSphere
    {g : RiemannianMetric 3 M} (N N' : EpsilonNeck g) where
  map : UnitTwoSphere → M
  smooth : ContMDiff (𝓡 2) (𝓡 3) ∞ map
  embedding : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ map
  image : Set M
  range_eq_image : Set.range map = image
  image_subset_first : image ⊆ N.carrier
  image_subset_second : image ⊆ N'.carrier

namespace EpsilonNeck.GraphicalSphere

variable {g : RiemannianMetric 3 M} {N N' : EpsilonNeck g}

def self (N : EpsilonNeck g) : EpsilonNeck.GraphicalSphere N N where
  map := fun p => N.coordinate_map (p, 0)
  smooth := N.centralSphere_contMDiff
  embedding := N.centralSphere_isSmoothEmbedding
  image := N.central_sphere
  range_eq_image := N.centralSphere_range
  image_subset_first := N.central_sphere_subset
  image_subset_second := N.central_sphere_subset

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
@[simp] theorem self_image (N : EpsilonNeck g) :
    (EpsilonNeck.GraphicalSphere.self N).image = N.central_sphere := rfl

end EpsilonNeck.GraphicalSphere

structure EpsilonNeck.SupportedHomeomorph
    {g : RiemannianMetric 3 M} (N N' : EpsilonNeck g) where
  graphical_sphere : EpsilonNeck.GraphicalSphere N N'
  homeomorph : M ≃ₜ M
  support : Set M
  support_compact : IsCompact support
  support_subset_overlap : support ⊆ N.carrier ∩ N'.carrier
  fixed_outside_support : ∀ x, x ∉ support → homeomorph x = x
  component_image : homeomorph '' connectedComponent N.center =
    connectedComponent N'.center
  sphere_image : homeomorph '' N.central_sphere = N'.central_sphere

namespace EpsilonNeck.SupportedHomeomorph

variable {g : RiemannianMetric 3 M}

def refl (N : EpsilonNeck g) : EpsilonNeck.SupportedHomeomorph N N where
  graphical_sphere := EpsilonNeck.GraphicalSphere.self N
  homeomorph := Homeomorph.refl M
  support := ∅
  support_compact := isCompact_empty
  support_subset_overlap := by simp
  fixed_outside_support := by simp
  component_image := by simp
  sphere_image := by simp

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
@[simp] theorem refl_homeomorph (N : EpsilonNeck g) :
    (EpsilonNeck.SupportedHomeomorph.refl N).homeomorph = Homeomorph.refl M := rfl

end EpsilonNeck.SupportedHomeomorph

end PoincareConjecture
