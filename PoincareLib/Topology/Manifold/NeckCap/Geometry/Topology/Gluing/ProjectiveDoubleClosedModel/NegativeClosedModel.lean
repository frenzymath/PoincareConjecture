import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.ProjectiveDoubleClosedModel.NegativeCover
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Projective.ProjectiveCoverModel
import PoincareLib.Topology.Manifold.NeckCap.Geometry.LocalClassification.Closed.ClosedComponentPacking

/-!
# The single projective component from the negative compact side

The actual full cover supplies the smooth and topological projective
models on the canonical open cap union. Morgan--Tian A.21, pp. 510-514;
negative-assembly derivation, section 6, and the accepted existential plan.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25.Topology3D

/-- The negative compact-side witness gives the single projective closed
component of the actual cap union. MT A.21, pp. 510-514; negative-assembly
derivation, sections 5-6. Both topology services remain explicit. -/
theorem capCertificates_nonempty_projective_component_of_negative_side
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (P1 : PoincareMT.StandardPuncturedProjectiveCover M C1.puncture C1.carrier)
    (P2 : PoincareMT.StandardPuncturedProjectiveCover M C2.puncture C2.carrier)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier))
    (d : NegativeProjectiveSideData C1 C2 P2) :
    Nonempty (ClosedComponentCertificate .realProjectiveThree
      (C1.carrier ∪ C2.carrier)) := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let U : TopologicalSpace.Opens M :=
    ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
  obtain ⟨C⟩ := NegativeProjectiveSideData.nonempty_smooth_cover hS hD P1 d
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
