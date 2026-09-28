import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem coordinate_map_mem_of_axial (N : EpsilonNeck g) (z : UnitTwoSphere × ℝ)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_map z ∈ N.carrier :=
  N.coordinate_map_mem ⟨mem_univ _, hz⟩

theorem coordinate_inverse_coordinate_map_of_axial (N : EpsilonNeck g)
    (z : UnitTwoSphere × ℝ) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_inverse (N.coordinate_map z) = z :=
  N.coordinate_inverse_coordinate_map ⟨mem_univ _, hz⟩

theorem region_eq_image_m28 (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) :
    N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b) := by
  ext x
  constructor
  · rintro ⟨hx, hax, hxb⟩
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hax, hxb⟩,
      N.coordinate_map_coordinate_inverse hx⟩
  · rintro ⟨z, ⟨_, haz, hzb⟩, rfl⟩
    have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨ha.trans_lt haz, hzb.trans_le hb⟩
    exact ⟨N.coordinate_map_mem_of_axial z hz, by
      simpa only [N.coordinate_inverse_coordinate_map_of_axial z hz] using And.intro haz hzb⟩

theorem region_open (N : EpsilonNeck g) (a b : ℝ) : IsOpen (N.region a b) := by
  have h := continuous_snd.comp_continuousOn N.coordinate_inverse_smooth.continuousOn
  exact h.isOpen_inter_preimage N.carrier_open isOpen_Ioo

theorem isCompact_coordinate_slab_intrinsic (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    IsCompact (N.coordinate_map '' (univ ×ˢ Icc a b)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

theorem coordinate_slab_subset_carrier_m28 (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    N.coordinate_map '' (univ ×ˢ Icc a b) ⊆ N.carrier := by
  rintro _ ⟨z, hz, rfl⟩
  exact N.coordinate_map_mem_of_axial z ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

end PoincareConjecture.EpsilonNeck
