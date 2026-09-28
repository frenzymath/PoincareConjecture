import PoincareConjecture.Proofs.M25.Topology3D.Gluing.TwoCapsClosedModel
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.MixedCapsClosedModel
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveDoubleClosedModel









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem exists_closed_component_of_two_caps
    (hS : PoincareConjecture.M25.Topology3D.SchoenfliesService)
    (hD : PoincareConjecture.M25.Topology3D.DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (hprojective : ∀ (A B : PoincareConjecture.M25.Topology3D.ClosedModelCapData g),
      A.model_kind = CapModelKind.puncturedProjective →
      B.model_kind = CapModelKind.puncturedProjective →
      IsCompact (A.carrier ∪ B.carrier) →
      ∃ kind : ClosedComponentKind,
        Nonempty (ClosedComponentCertificate kind (A.carrier ∪ B.carrier)))
    (C1 C2 : PoincareConjecture.M25.Topology3D.ClosedModelCapData g)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    ∃ kind : ClosedComponentKind,
      Nonempty (ClosedComponentCertificate kind (C1.carrier ∪ C2.carrier)) := by
  cases h1 : C1.model_kind with
  | euclidean =>
    cases h2 : C2.model_kind with
    | euclidean =>
      exact ⟨.threeSphere,
        PoincareConjecture.M25.Topology3D.capCertificates_nonempty_threeSphere_component_of_services
          hS hD C1 C2 h1 h2 hcompact⟩
    | puncturedProjective =>
      refine ⟨.realProjectiveThree, ?_⟩
      rw [Set.union_comm]
      exact PoincareConjecture.M25.Topology3D.capCertificates_nonempty_projective_component_of_services
        hS hD C2 C1 h2 h1 (by rwa [Set.union_comm])
  | puncturedProjective =>
    cases h2 : C2.model_kind with
    | euclidean =>
      exact ⟨.realProjectiveThree,
        PoincareConjecture.M25.Topology3D.capCertificates_nonempty_projective_component_of_services
          hS hD C1 C2 h1 h2 hcompact⟩
    | puncturedProjective =>
      exact hprojective C1 C2 h1 h2 hcompact


namespace M25.Topology3D



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

end PoincareConjecture
