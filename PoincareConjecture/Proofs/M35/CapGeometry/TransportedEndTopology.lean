import PoincareConjecture.Proofs.M35.CapGeometry.CarrierTopology









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapCertificate



theorem transported_end_attachment
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (C : CapCertificate g)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (hClosure : closure C.carrier ⊆ phi.source) :
    phi '' C.boundary_sphere = phi '' C.carrier ∩ frontier (phi '' C.end_neck.carrier) ∧
      phi '' C.boundary_sphere ⊆
        closure (phi '' C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2)) := by
  have hU : C.carrier ⊆ phi.source := subset_closure.trans hClosure
  have hrelation : phi.toOpenPartialHomeomorph.IsImage C.end_neck.carrier
      (phi '' C.end_neck.carrier) := by
    intro x hx
    constructor
    · rintro ⟨z, hz, heq⟩
      exact phi.toPartialEquiv.injOn (hU (C.end_neck_subset hz)) hx heq ▸ hz
    · intro hz
      exact mem_image_of_mem phi hz
  constructor
  · ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := C.boundary_eq_end_frontier ▸ hx
      exact ⟨⟨x, hx'.1, rfl⟩, (hrelation.frontier (hU hx'.1)).mpr hx'.2⟩
    · rintro ⟨⟨x, hx, rfl⟩, hfrontier⟩
      refine ⟨x, ?_, rfl⟩
      rw [C.boundary_eq_end_frontier]
      exact ⟨hx, (hrelation.frontier (hU hx)).mp hfrontier⟩
  · have hregion : C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2) ⊆ C.carrier :=
      fun _ hz => C.end_neck_subset hz.1
    have hcontinuous : ContinuousOn phi
        (closure (C.end_neck.region (-C.epsilon⁻¹) (-C.epsilon⁻¹ / 2))) :=
      phi.contMDiffOn_toFun.continuousOn.mono ((closure_mono hregion).trans hClosure)
    exact (image_mono C.boundary_subset_negative_end_closure).trans hcontinuous.image_closure

end PoincareConjecture.CapCertificate
