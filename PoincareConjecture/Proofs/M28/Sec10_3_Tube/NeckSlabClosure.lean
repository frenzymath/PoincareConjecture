import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckRegions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem closure_region_eq_coordinate_slab (N : EpsilonNeck g) {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hab : a < b) (hb : b < N.epsilon⁻¹) :
    closure (N.region a b) = N.coordinate_map '' (univ ×ˢ Icc a b) := by
  have hcl : closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) = univ ×ˢ Icc a b := by
    rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
  have hcompact : IsCompact (closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b)) := by
    rw [hcl]
    exact isCompact_univ.prod isCompact_Icc
  have hcont : ContinuousOn N.coordinate_map
      (closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b)) := by
    rw [hcl]
    exact N.coordinate_map_smooth.continuousOn.mono
      (fun _ hz => ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩)
  rw [N.region_eq_image_m28 ha.le hb.le]
  have hh := image_closure_of_isCompact hcompact hcont
  rw [hcl] at hh
  exact hh.symm

end PoincareConjecture.EpsilonNeck
