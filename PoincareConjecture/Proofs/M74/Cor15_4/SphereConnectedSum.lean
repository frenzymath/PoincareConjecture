import PoincareConjecture.Proofs.M74.Cor15_4.CanonicalPuncturedSphereEnd
import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorptionActualAssembly
import PoincareConjecture.Proofs.M74.Cor15_4.StepPreservesSphereUnion











set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SmoothConnectedSumData

open M25.Topology3D




theorem nonempty_diffeomorph_threeSphere
    {A B C : GeneralizedSliceCarrier.{u}} (S : SmoothConnectedSumData A B C)
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    (hA : Nonempty (Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞))
    (hB : Nonempty (Diffeomorph (𝓡 3) (𝓡 3) B.carrier ThreeSphere ∞)) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞) := by
  obtain ⟨dA⟩ := hA
  obtain ⟨dB⟩ := hB
  obtain ⟨EA, epsilonA, hApos, hAlt, hEA⟩ :=
    S.first_ball.exists_canonicalPuncturedSphereEnd dA hS hD
  obtain ⟨EB, epsilonB, hBpos, hBlt, hEB⟩ :=
    S.second_ball.exists_canonicalPuncturedSphereEnd dB hS hD
  exact S.nonempty_sphereDiffeomorph_of_canonicalEnds
    EA epsilonA hApos hAlt hEA EB epsilonB hBpos hBlt hEB hD

end PoincareConjecture.SmoothConnectedSumData

namespace PoincareConjecture.M74

open M25.Topology3D



theorem connectedSumReduction_of_topology_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService) :
    M74ConnectedSumReductionStatement.{u} :=
  connectedSumReduction_of_binary_sphere_identity
    (fun _ _ _ S hA hB => S.nonempty_diffeomorph_threeSphere hS hD hA hB)

end PoincareConjecture.M74
