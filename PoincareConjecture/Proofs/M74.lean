import PoincareConjecture.Statements.M74ConnectedSumReduction
import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.Service
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.HorizonSchoenfliesService
import PoincareConjecture.Proofs.M74.Cor15_4.SphereConnectedSum

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m74ConnectedSumReduction :
    M74ConnectedSumReductionStatement.{u} :=
  M74.connectedSumReduction_of_topology_services
    M25.Topology3D.schoenfliesService_from_main
    M25.Topology3D.diffSphereIsotopyService

end PoincareConjecture
