import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.CanonicalPuncturedSphereEnd
import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.CollarAbsorptionActualAssembly
import PoincareLib.Topology.Manifold.Surgery.Reduction.Assembly.StepPreservesSphereUnion

/-!
# The binary sphere identity and finite connected-sum reduction

The explicit lower topology services give canonical ends for both source
spheres. Their actual connected-sum collar then gives the sphere identity,
which supplies the previously proved finite reduction. The two services
remain hypotheses of these helpers until their published providers are
available. Source: MT Corollary 15.4(2), pp. 358-359.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.SmoothConnectedSumData

open M25.Topology3D

/-- The connected sum of two standard smooth spheres is a standard sphere,
given the two explicit lower topology services
(MT Corollary 15.4(2), pp. 358-359). -/
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

end PoincareMT.SmoothConnectedSumData

namespace PoincareMT.M74

open M25.Topology3D

/-- The frozen connected-sum reduction follows from the two explicit lower
topology services (MT Corollary 15.4(2), pp. 358-359). -/
theorem connectedSumReduction_of_topology_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService) :
    M74ConnectedSumReductionStatement.{u} :=
  connectedSumReduction_of_binary_sphere_identity
    (fun _ _ _ S hA hB => S.nonempty_diffeomorph_threeSphere hS hD hA hB)

end PoincareMT.M74
