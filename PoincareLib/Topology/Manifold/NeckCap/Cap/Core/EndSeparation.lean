import PoincareLib.Topology.Manifold.NeckCap.Cap.Core.BoundaryTransport
import PoincareLib.Topology.Manifold.NeckCap.Cap.Separation
import PoincareLib.Topology.Manifold.NeckCap.Overlap.SliceAgreement

/-!
# Separation by the original end neck of a cap

A strict boundary-collar slice lies in the cap's end neck. At the universal
slice-agreement threshold, the end neck therefore inherits the separating
label of the boundary neck, without changing either neck certificate.

Reference: Morgan--Tian, Lemmas A.17--A.18, pp. 506--507, and
Proposition A.21, pp. 508--514.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

/-- Every sufficiently small cap has a separating original end neck, at a
threshold independent of the cap and the ambient manifold. -/
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

end PoincareMT.CapCertificate
