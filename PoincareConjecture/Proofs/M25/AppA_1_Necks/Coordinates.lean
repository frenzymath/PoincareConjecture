import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected














set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)


theorem zero_mem_interval : (0 : ℝ) ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have hpos := inv_pos.mpr N.epsilon_pos
  exact ⟨neg_lt_zero.mpr hpos, hpos⟩



theorem coordinate_inverse_map (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_inverse (N.coordinate_map z) = z :=
  N.coordinate_inverse_coordinate_map ⟨Set.mem_univ _, hz⟩



theorem coordinate_map_inverse {x : M} (hx : x ∈ N.carrier) :
    N.coordinate_map (N.coordinate_inverse x) = x :=
  N.coordinate_map_coordinate_inverse hx



theorem coordinate_map_image :
    N.coordinate_map '' (Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) =
      N.carrier := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact N.coordinate_map_mem hz
  · intro x hx
    exact ⟨N.coordinate_inverse x, N.coordinate_inverse_mem x hx,
      N.coordinate_map_inverse hx⟩



theorem coordinate_map_injOn : Set.InjOn N.coordinate_map
    (Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  intro z hz w hw h
  have hinv := congrArg N.coordinate_inverse h
  simpa only [N.coordinate_inverse_map z hz.2,
    N.coordinate_inverse_map w hw.2] using hinv

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem m25_carrier_subset_connectedComponent : N.carrier ⊆ connectedComponent N.center :=
  N.isConnected_carrier.subset_connectedComponent
    (N.central_sphere_subset N.center_on_central_sphere)



theorem m25_component_diff_central_sphere_nonempty :
    (connectedComponent N.center \ N.central_sphere).Nonempty := by
  have hpos := inv_pos.mpr N.epsilon_pos
  let z : RoundCylinderSpace := ((N.coordinate_inverse N.center).1, N.epsilon⁻¹ / 2)
  have hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    dsimp [z]
    constructor <;> linarith
  refine ⟨N.coordinate_map z, N.m25_carrier_subset_connectedComponent
    (N.coordinate_map_mem ⟨Set.mem_univ _, hz⟩), ?_⟩
  intro hs
  have hzero := ((N.mem_central_sphere_iff _).mp hs).2
  rw [N.coordinate_inverse_map z hz] at hzero
  dsimp [z] at hzero
  linarith



theorem m25_isSeparating_iff_not_isNonseparating : N.IsSeparating ↔ ¬ N.IsNonseparating :=
  and_iff_right N.m25_component_diff_central_sphere_nonempty



theorem m25_isSeparating_or_isNonseparating : N.IsSeparating ∨ N.IsNonseparating := by
  rw [N.m25_isSeparating_iff_not_isNonseparating]
  exact (Classical.em _).symm

end PoincareConjecture.EpsilonNeck
