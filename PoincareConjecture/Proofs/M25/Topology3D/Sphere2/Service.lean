import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.Reduction
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CompactIsotopy

set_option autoImplicit false

namespace PoincareConjecture.M25.Topology3D

theorem diffSphereIsotopyService : DiffSphereIsotopyService :=
  diffSphereIsotopyService_of_compactPlanarIsotopyProperty compactPlanarIsotopyProperty

end PoincareConjecture.M25.Topology3D
