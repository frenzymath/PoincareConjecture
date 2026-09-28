import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected
import Mathlib.Topology.Homeomorph.Lemmas





















set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

namespace EpsilonNeck

variable {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem carrier_subset_connectedComponent : N.carrier ⊆ connectedComponent N.center :=
  N.isConnected_carrier.subset_connectedComponent
    (N.central_sphere_subset N.center_on_central_sphere)


theorem component_diff_central_sphere_nonempty :
    (connectedComponent N.center \ N.central_sphere).Nonempty := by
  have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let z : NeckDomain N.epsilon :=
    ((N.coordinate_inverse N.center).1, ⟨N.epsilon⁻¹ / 2, by constructor <;> linarith⟩)
  refine ⟨N.coordinate z, N.carrier_subset_connectedComponent (N.coordinate z).property, ?_⟩
  intro hz
  have hzero := ((N.mem_central_sphere_iff _).mp hz).2
  rw [N.coordinate_inverse_left] at hzero
  change N.epsilon⁻¹ / 2 = 0 at hzero
  linarith

theorem isSeparating_iff_not_isNonseparating : N.IsSeparating ↔ ¬ N.IsNonseparating :=
  and_iff_right N.component_diff_central_sphere_nonempty

theorem isSeparating_or_isNonseparating : N.IsSeparating ∨ N.IsNonseparating := by
  rw [N.isSeparating_iff_not_isNonseparating]
  exact (Classical.em _).symm

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem not_isSeparating_and_isNonseparating : ¬ (N.IsSeparating ∧ N.IsNonseparating) := by
  rintro ⟨hs, hn⟩
  exact hs.2 hn

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem isNonseparating_iff_of_homeomorph (N' : EpsilonNeck g) (e : M ≃ₜ M)
    (hcomponent : e '' connectedComponent N.center = connectedComponent N'.center)
    (hsphere : e '' N.central_sphere = N'.central_sphere) :
    N.IsNonseparating ↔ N'.IsNonseparating := by
  unfold IsNonseparating
  rw [← hcomponent, ← hsphere, ← Set.image_sdiff e.injective, e.isConnected_image]

theorem isSeparating_iff_of_homeomorph (N' : EpsilonNeck g) (e : M ≃ₜ M)
    (hcomponent : e '' connectedComponent N.center = connectedComponent N'.center)
    (hsphere : e '' N.central_sphere = N'.central_sphere) :
    N.IsSeparating ↔ N'.IsSeparating := by
  rw [N.isSeparating_iff_not_isNonseparating, N'.isSeparating_iff_not_isNonseparating,
    N.isNonseparating_iff_of_homeomorph N' e hcomponent hsphere]

end EpsilonNeck

end PoincareConjecture
