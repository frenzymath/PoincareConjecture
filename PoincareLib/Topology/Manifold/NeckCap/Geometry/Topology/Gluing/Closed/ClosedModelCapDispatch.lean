import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Two.TwoCapsClosedModel
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Mixed.MixedCapsClosedModel
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Projective.ProjectiveDoubleClosedModel

/-!
# Closed models of two light caps

The kind dispatch uses only the canonical metric-free cap data. The
actual-cap compatibility entry projects full certificates once.
Morgan--Tian A.21, pp. 510-514; light-cap-dispatch plan.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Compact two-cap unions are classified by their actual cap kinds,
conditional on the two services and the projective-pair construction.
MT A.21, p. 514; reviewed entry-assembly-adoption derivation. -/
theorem exists_closed_component_of_two_caps
    (hS : PoincareMT.M25.Topology3D.SchoenfliesService)
    (hD : PoincareMT.M25.Topology3D.DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (hprojective : ∀ (A B : PoincareMT.M25.Topology3D.ClosedModelCapData g),
      A.model_kind = CapModelKind.puncturedProjective →
      B.model_kind = CapModelKind.puncturedProjective →
      IsCompact (A.carrier ∪ B.carrier) →
      ∃ kind : ClosedComponentKind,
        Nonempty (ClosedComponentCertificate kind (A.carrier ∪ B.carrier)))
    (C1 C2 : PoincareMT.M25.Topology3D.ClosedModelCapData g)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (C1.carrier ∪ C2.carrier)) := by
  cases h1 : C1.model_kind with
  | euclidean =>
    cases h2 : C2.model_kind with
    | euclidean =>
      exact ⟨.threeSphere,
        PoincareMT.M25.Topology3D.capCertificates_nonempty_threeSphere_component_of_services
          hS hD C1 C2 h1 h2 hcompact⟩
    | puncturedProjective =>
      refine ⟨.realProjectiveThree, ?_⟩
      rw [Set.union_comm]
      exact PoincareMT.M25.Topology3D.capCertificates_nonempty_projective_component_of_services
        hS hD C2 C1 h2 h1 (by rwa [Set.union_comm])
  | puncturedProjective =>
    cases h2 : C2.model_kind with
    | euclidean =>
      exact ⟨.realProjectiveThree,
        PoincareMT.M25.Topology3D.capCertificates_nonempty_projective_component_of_services
          hS hD C1 C2 h1 h2 hcompact⟩
    | puncturedProjective =>
      exact hprojective C1 C2 h1 h2 hcompact


namespace M25.Topology3D

/-- Classify two light caps using the Euclidean, mixed and existential
projective producers. MT A.21, pp. 510-514; light-cap-dispatch plan. -/
theorem closedModelCapData_exists_closed_component_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (C1.carrier ∪ C2.carrier)) :=
  exists_closed_component_of_two_caps hS hD
    (capCertificates_exists_closed_component_of_projective_services hS hD)
    C1 C2 hcompact

/-- Full caps enter the same classifier by their canonical light
projections. MT A.21, pp. 510-514; light-cap-dispatch plan. -/
theorem capCertificates_exists_closed_component_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : CapCertificate g)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (C1.carrier ∪ C2.carrier)) :=
  closedModelCapData_exists_closed_component_of_services hS hD
    (ClosedModelCapData.ofCapCertificate C1) (ClosedModelCapData.ofCapCertificate C2) hcompact

end M25.Topology3D

end PoincareMT
