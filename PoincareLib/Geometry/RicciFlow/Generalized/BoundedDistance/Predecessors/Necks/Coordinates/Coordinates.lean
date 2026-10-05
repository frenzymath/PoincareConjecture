import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected

/-!
# Coordinates and component-relative separation of a neck

Morgan--Tian Definition 2.18, printed p. 31, gives a neck its actual product
coordinates. We record their inverse identities on the specified domains,
connectedness of the carrier, and nonemptiness of the central sphere's
complement in the component of the center. The last fact is used in the
corrected Appendix A.19-A.20 conventions (pp. 507-508); see the component
separation repair dated 2026-09-18 and the uniform-label supplement dated
2026-09-20 in `reviews/`. Coordinate identities and carrier connectedness
are reused from the lower library imported by M20.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- The central slice lies strictly inside the neck interval (Def. 2.18, p. 31). -/
theorem zero_mem_interval : (0 : ℝ) ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have hpos := inv_pos.mpr N.epsilon_pos
  exact ⟨neg_lt_zero.mpr hpos, hpos⟩

/-- The displayed inverse really inverts product coordinates inside the
neck interval (Def. 2.18, p. 31). -/
theorem coordinate_inverse_map (z : RoundCylinderSpace)
    (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_inverse (N.coordinate_map z) = z :=
  N.coordinate_inverse_coordinate_map ⟨Set.mem_univ _, hz⟩

/-- The coordinate map inverts the displayed inverse on the carrier
(Def. 2.18, p. 31). -/
theorem coordinate_map_inverse {x : M} (hx : x ∈ N.carrier) :
    N.coordinate_map (N.coordinate_inverse x) = x :=
  N.coordinate_map_coordinate_inverse hx

/-- The full product domain has exactly the specified neck carrier as image
(Def. 2.18, p. 31). -/
theorem coordinate_map_image :
    N.coordinate_map '' (Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) =
      N.carrier := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    exact N.coordinate_map_mem hz
  · intro x hx
    exact ⟨N.coordinate_inverse x, N.coordinate_inverse_mem x hx,
      N.coordinate_map_inverse hx⟩

/-- Product coordinates are injective on their actual domain
(Def. 2.18, p. 31). -/
theorem coordinate_map_injOn : Set.InjOn N.coordinate_map
    (Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
  intro z hz w hw h
  have hinv := congrArg N.coordinate_inverse h
  simpa only [N.coordinate_inverse_map z hz.2,
    N.coordinate_inverse_map w hw.2] using hinv

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

/-- The whole neck lies in the center's connected component, including
when the ambient manifold is disconnected (A.19, pp. 507-508, corrected). -/
theorem m25_carrier_subset_connectedComponent : N.carrier ⊆ connectedComponent N.center :=
  N.isConnected_carrier.subset_connectedComponent
    (N.central_sphere_subset N.center_on_central_sphere)

/-- A positive longitudinal point is outside the central sphere but inside
the center's component (A.19-A.20, pp. 507-508, component-relative repair). -/
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

/-- The two neck separation labels are complementary because the component
complement is nonempty (A.20, p. 508; uniform-label supplement, 2026-09-20). -/
theorem m25_isSeparating_iff_not_isNonseparating : N.IsSeparating ↔ ¬ N.IsNonseparating :=
  and_iff_right N.m25_component_diff_central_sphere_nonempty

/-- Every neck has one of the two component-relative separation labels
(A.20, p. 508; uniform-label supplement, 2026-09-20). -/
theorem m25_isSeparating_or_isNonseparating : N.IsSeparating ∨ N.IsNonseparating := by
  rw [N.m25_isSeparating_iff_not_isNonseparating]
  exact (Classical.em _).symm

end PoincareMT.EpsilonNeck
