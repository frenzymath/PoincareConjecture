import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Sphere.Reduction
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Plane.Isotopy.CompactIsotopy

/-!
# Sphere isotopy service assembly

Smale, Theorem 6, and Munkres, Theorem 1.3. The compact planar isotopy
theorem supplies the final input to the sphere reduction.
-/

set_option autoImplicit false

namespace PoincareMT.M25.Topology3D

/-- The sphere isotopy service from the exact compact planar property;
Smale, Theorem 6, and Munkres, Theorem 1.3. -/
theorem diffSphereIsotopyService : DiffSphereIsotopyService :=
  diffSphereIsotopyService_of_compactPlanarIsotopyProperty compactPlanarIsotopyProperty

end PoincareMT.M25.Topology3D
