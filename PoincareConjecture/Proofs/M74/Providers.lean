import PoincareConjecture.Proofs.M73.Providers
import PoincareConjecture.Proofs.M74









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}

def m74ReductionInputFromSphereFactors
    (I : M72ReconstructionInput N) (C : M72ReconstructionConclusion I)
    (S : M73SphereFactorConclusion I C) :
    M74ReductionInput C.pieces (I.global.certificate.flow.slice 0) where
  assembly := C.assembly
  target_nonempty := C.target_nonempty
  target_connected := C.target_connected
  factor_sphere := fun j => ⟨S.factor_sphere j⟩

theorem m74Reduction_from_M72_M73 [SimplyConnectedSpace M]
    (I : M72ReconstructionInput N) :
    Nonempty (M74ReductionConclusion (I.global.certificate.flow.slice 0)) := by
  obtain ⟨C, ⟨S⟩⟩ := m73SphereFactors_from_M72 I
  exact m74ConnectedSumReduction C.pieces (I.global.certificate.flow.slice 0)
    (m74ReductionInputFromSphereFactors I C S)

end PoincareConjecture
