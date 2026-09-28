import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.ClosedModels.ProjectivePair
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ProjectiveCoordinates













set_option autoImplicit false

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem nonempty_two_projective_cap_closedComponentCertificate (C D : CapCertificate g)
    (hC : C.model_kind = .puncturedProjective) (hD : D.model_kind = .puncturedProjective)
    (hcompact : IsCompact (C.carrier ∪ D.carrier))
    (hcomponent : ∃ x : M, C.carrier ∪ D.carrier = connectedComponent x) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (C.carrier ∪ D.carrier)) := by
  obtain ⟨S⟩ := C.nonempty_projective_cover hC
  obtain ⟨SD⟩ := D.nonempty_projective_cover hD
  exact ClosedModels.nonempty_projective_pair_certificate
    ⟨C.carrier, C.carrier_open⟩ ⟨D.carrier, D.carrier_open⟩ S SD hcompact hcomponent

end PoincareConjecture.CapCertificate
