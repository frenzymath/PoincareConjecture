import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem coordinate_slab_subset_carrier {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    N.coordinate_map '' (univ ×ˢ Icc a b) ⊆ N.carrier := by
  rintro x ⟨z, hz, rfl⟩
  exact N.coordinate_map_mem ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

theorem carrier_subset_ends_union_slab (a b : ℝ) :
    N.carrier ⊆ N.region (-N.epsilon⁻¹) a ∪
      N.coordinate_map '' (univ ×ˢ Icc a b) ∪ N.region b N.epsilon⁻¹ := by
  intro x hx
  have hz := (N.coordinate_inverse_mem x hx).2
  by_cases hxa : (N.coordinate_inverse x).2 < a
  · exact Or.inl (Or.inl ⟨hx, hz.1, hxa⟩)
  by_cases hxb : b < (N.coordinate_inverse x).2
  · exact Or.inr ⟨hx, hxb, hz.2⟩
  exact Or.inl (Or.inr ⟨N.coordinate_inverse x,
    ⟨mem_univ _, le_of_not_gt hxa, le_of_not_gt hxb⟩,
    N.coordinate_map_coordinate_inverse hx⟩)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem frontier_subset_closure_ends {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    frontier N.carrier ⊆ closure (N.region (-N.epsilon⁻¹) a) ∪
      closure (N.region b N.epsilon⁻¹) := by
  intro x hx
  have hxc := closure_mono (N.carrier_subset_ends_union_slab a b)
    (frontier_subset_closure hx)
  rw [closure_union, closure_union, (N.isCompact_coordinate_slab ha hb).isClosed.closure_eq]
    at hxc
  rcases hxc with (hneg | hmid) | hpos
  · exact Or.inl hneg
  · exact False.elim ((N.carrier_open.frontier_eq ▸ hx).2
      (N.coordinate_slab_subset_carrier ha hb hmid))
  · exact Or.inr hpos

theorem frontier_center_overlap_end (N' : EpsilonNeck g)
    (hx : N'.center ∈ frontier N.carrier) {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    (N'.carrier ∩ N.region (-N.epsilon⁻¹) a).Nonempty ∨
      (N'.carrier ∩ N.region b N.epsilon⁻¹).Nonempty := by
  have hnhds := N'.carrier_open.mem_nhds
    (N'.central_sphere_subset N'.center_on_central_sphere)
  rcases N.frontier_subset_closure_ends ha hb hx with hneg | hpos
  · exact Or.inl (mem_closure_iff_nhds.mp hneg _ hnhds)
  · exact Or.inr (mem_closure_iff_nhds.mp hpos _ hnhds)

end PoincareConjecture.EpsilonNeck
