import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBirthStar
import PoincareConjecture.Proofs.M76.Mathlib.RadialStar

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

theorem exists_positive_link_point_of_surface_accumulation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    (hpos : (0 : E) ∈ closure (K.space ∩ {x | 0 < L x})) :
    ∃ y ∈ (K.link 0).space, 0 < L y := by
  obtain ⟨ε, hε, hnear⟩ := K.exists_ball_inter_space_subset_closedStar hK hzero
  obtain ⟨x, hxball, hxK, hxL⟩ := mem_closure_iff.mp hpos (Metric.ball 0 ε)
    Metric.isOpen_ball (Metric.mem_ball_self hε)
  change 0 < L x at hxL
  have hxzero : x ≠ 0 := by
    intro hx
    simp only [hx, map_zero, lt_self_iff_false] at hxL
  obtain ⟨y, hy, r, hr, hxy⟩ := exists_linkPoint_smul (hnear ⟨hxK, hxball⟩) hxzero
  refine ⟨y, hy, ?_⟩
  rw [hxy, map_smul, smul_eq_mul] at hxL
  exact (mul_pos_iff_of_pos_left hr.1).mp hxL

theorem exists_both_link_signs_of_surface_accumulation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    (hpos : (0 : E) ∈ closure (K.space ∩ {x | 0 < L x}))
    (hneg : (0 : E) ∈ closure (K.space ∩ {x | L x < 0})) :
    (∃ y ∈ (K.link 0).space, 0 < L y) ∧
      ∃ y ∈ (K.link 0).space, L y < 0 := by
  refine ⟨K.exists_positive_link_point_of_surface_accumulation hK hzero L hpos, ?_⟩
  have hneg' : (0 : E) ∈ closure (K.space ∩ {x | 0 < (-L) x}) := by
    simpa only [LinearMap.neg_apply, neg_pos] using hneg
  simpa only [LinearMap.neg_apply, neg_pos] using
    K.exists_positive_link_point_of_surface_accumulation hK hzero (-L) hneg'

end Geometry.SimplicialComplex
