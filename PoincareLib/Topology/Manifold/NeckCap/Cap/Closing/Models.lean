import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Certificate
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Euclidean
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Mixed.TwoCaps
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Mixed.Exterior
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Projective.TwoCaps
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.Tube.Models
import PoincareLib.Topology.Manifold.NeckCap.Cap.Core.CollarFilling
import PoincareLib.Topology.Manifold.NeckCap.Cap.Closing.ProjectiveModel
import PoincareLib.Topology.Manifold.NeckCap.Cap.Projective.CollarFilling
import PoincareLib.Topology.Manifold.Diffeomorph.SphereCharts

/-!
# Smooth models of compact cap unions

The topological model and its transport are constructed from the smooth
model on the original component. All two-cap branches supply exact closed
certificates: the Euclidean pair gives the sphere, the mixed pair gives
projective space, and the projective pair gives projective space or its
connected sum. Absorption along matching full collars reduces the original
doubly capped tube to the same smooth open-model classification.

Reference: Morgan--Tian, Proposition A.21 and Claims A.23--A.24,
pp. 508--514.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

/-- Compact components covered by two sufficiently small caps have a smooth
closed standard model on their original carrier. -/
theorem exists_two_cap_closed_model_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (C D : CapCertificate g),
        C.epsilon = D.epsilon → C.epsilon ≤ ε₀ →
        IsCompact (C.carrier ∪ D.carrier) →
        (∃ x : M, C.carrier ∪ D.carrier = connectedComponent x) →
        ∃ kind : ClosedComponentKind,
          Nonempty (ClosedComponentCertificate kind (C.carrier ∪ D.carrier)) := by
  refine ⟨1 / 200, by norm_num, le_rfl, ?_⟩
  intro M _ _ _ _ _ _ _ g C D _ _ hcompact hcomponent
  cases hC : C.model_kind with
  | euclidean =>
    cases hD : D.model_kind with
    | euclidean =>
      exact ⟨.threeSphere,
        C.nonempty_two_euclidean_cap_closedComponentCertificate D hC hD hcompact hcomponent⟩
    | puncturedProjective =>
      refine ⟨.realProjectiveThree, ?_⟩
      simpa only [union_comm] using
        D.nonempty_mixed_cap_closedComponentCertificate C hD hC
          (union_comm C.carrier D.carrier ▸ hcompact)
          (union_comm C.carrier D.carrier ▸ hcomponent)
  | puncturedProjective =>
    cases hD : D.model_kind with
    | euclidean =>
      exact ⟨.realProjectiveThree,
        C.nonempty_mixed_cap_closedComponentCertificate D hC hD hcompact hcomponent⟩
    | puncturedProjective =>
      exact C.nonempty_two_projective_cap_closedComponentCertificate D hC hD hcompact hcomponent

/-- The same classification for the original carrier of a doubly capped
tube, retaining its complete opposite attachments and disjoint closed cores. -/
theorem exists_double_capped_tube_closed_model_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (T : DoubleCappedTubeCertificate g),
        T.cap₁.epsilon = T.cap₂.epsilon →
        T.cap₁.epsilon = T.tube.epsilon → T.cap₁.epsilon ≤ ε₀ →
        (∃ x : M, T.carrier = connectedComponent x) →
        ∃ kind : ClosedComponentKind,
          Nonempty (ClosedComponentCertificate kind T.carrier) := by
  exact DoubleCappedTubeCertificate.exists_closed_model_threshold

end PoincareMT.CapCertificate
