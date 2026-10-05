import PoincareLib.Topology.Manifold.Surgery.Reduction.Statement
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Sphere.Service
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Gluing.SchoenfliesService
import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.SphereConnectedSum

/-!
# M74 proof entry

The finite connected-sum reduction applies the published M25 topology
services to the componentwise sphere identity. M72 and M73 are not inputs
to this theorem. Source: Morgan--Tian Corollary 15.4(2), pp. 358--359.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Given a finite smooth connected-sum assembly whose target is nonempty
and connected, and a smooth diffeomorphism from each original factor to the
unit three-sphere, construct a smooth diffeomorphism of the target to that
sphere. The proof owns the sphere connected-sum identity for the supplied
collared balls and sphere gluing, followed by componentwise finite induction.
No target-to-sphere map is assumed. Source: Morgan--Tian Corollary 15.4(2),
pp. 358--359, after Proposition 15.3, pp. 357--358. The M38 separating-neck
correction is already encoded by the genuine connected-sum operations. -/
theorem m74ConnectedSumReduction :
    M74ConnectedSumReductionStatement.{u} :=
  M74.connectedSumReduction_of_topology_services
    M25.Topology3D.schoenfliesService_from_main
    M25.Topology3D.diffSphereIsotopyService

end PoincareMT
