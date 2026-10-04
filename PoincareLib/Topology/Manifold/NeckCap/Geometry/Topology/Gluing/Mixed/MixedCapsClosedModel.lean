import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Mixed.MixedCapCover
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Projective.ProjectiveCoverModel
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Closed.ClosedComponentPacking

/-!
# The closed component of a projective cap and a Euclidean cap

The actual conditional smooth antipodal cover supplies both standard
models of the frozen closed-component certificate on the original cap
union. Connectedness follows from its continuous sphere cover. This is
the mixed two-cap case of Morgan--Tian A.21, pp. 510-514; see the approved
mixed-cap-assembly-plan, PCA7. Both topology services remain hypotheses.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25.Topology3D

/-- The compact union of a projective cap and a Euclidean cap has its full
smooth projective component certificate, conditional on the two topology
services. Morgan--Tian A.21, pp. 510-514; mixed-cap assembly, PCA7. -/
theorem capCertificates_nonempty_projective_component_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (hkind1 : C1.model_kind = CapModelKind.puncturedProjective)
    (hkind2 : C2.model_kind = CapModelKind.euclidean)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    Nonempty (ClosedComponentCertificate .realProjectiveThree
      (C1.carrier ∪ C2.carrier)) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let U : TopologicalSpace.Opens M :=
    ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
  obtain ⟨C⟩ := capCertificates_exists_projective_smooth_cover_of_services
    hS hD C1 C2 hkind1 hkind2 hcompact
  obtain ⟨e, _⟩ := C.exists_projective_homeomorph
  let : ConnectedSpace UnitThreeSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  have hconnected : ConnectedSpace U :=
    C.surjective.connectedSpace C.local_diffeomorph.isLocalHomeomorph.continuous
  exact ClosedComponentCertificate.nonempty_of_compact_connected_opens
    .realProjectiveThree U hcompact (isConnected_iff_connectedSpace.mpr hconnected)
    e ⟨C⟩

end PoincareMT.M25.Topology3D
