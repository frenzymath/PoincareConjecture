import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.BoundaryTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Separation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.SliceAgreement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_end_neck_separating_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ → C.end_neck.IsSeparating := by
  obtain ⟨ε₀, hε₀, hsmall, hagree⟩ := EpsilonNeck.exists_contained_slice_separation_agreement.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hC
  obtain ⟨a, ha, hslice⟩ := C.exists_boundary_slice_in_end
  exact (hagree C.end_neck C.boundary_neck (C.end_neck_epsilon.trans_le hC)
    (C.boundary_neck_epsilon.trans_le hC) ha hslice).1.mp C.boundary_neck_isSeparating

end PoincareConjecture.CapCertificate
