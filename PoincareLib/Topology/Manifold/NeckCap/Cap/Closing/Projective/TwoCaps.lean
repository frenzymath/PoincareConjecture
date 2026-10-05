import PoincareLib.Topology.Manifold.Diffeomorph.ClosedModels.ProjectivePair
import PoincareLib.Topology.Manifold.NeckCap.Cap.ProjectiveCoordinates

/-!
# Smooth closed models for an original union of two projective caps

A projective enclosing piece leaves a compact sphere-bounded side in the
second projective cap. Its smooth ball or projective-core classification
gives projective space or the projective connected sum on the original
union, retaining the full separating collar.

Reference: Morgan--Tian, Proposition A.21 and Claims A.23--A.24, pp. 508--514;
Hatcher, Notes on Basic 3-Manifold Topology (2014), Theorem 1.1, pp. 1--5.
-/

set_option autoImplicit false

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

/-- A compact ambient component covered by two projective caps has an
exact smooth closed standard certificate on the original union. -/
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

end PoincareMT.CapCertificate
