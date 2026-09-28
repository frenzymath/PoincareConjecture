import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckRestriction
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization
import Mathlib.Analysis.Normed.Module.Connected










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem coordinate_map_coordinate_inverse {x : M} (hx : x ∈ N.carrier) :
    N.coordinate_map (N.coordinate_inverse x) = x := by
  have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
  rw [N.coordinate_map_eq] at h
  exact h



theorem region_isOpen (a b : ℝ) : IsOpen (N.region a b) :=
  N.coordinate_inverse_smooth.continuousOn.snd.isOpen_inter_preimage
    N.carrier_open isOpen_Ioo



theorem region_eq_image {a b : ℝ} (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) :
    N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b) := by
  ext x
  constructor
  · intro hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hzN : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩
    refine ⟨N.coordinate_map_mem_of_axial_mem hzN, ?_⟩
    rw [N.coordinate_inverse_coordinate_map_of_axial_mem hzN]
    exact hz.2



theorem region_isPreconnected {a b : ℝ}
    (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹) : IsPreconnected (N.region a b) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  let : PreconnectedSpace UnitTwoSphere :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_sphere hrank 0 1)
  rw [N.region_eq_image ha hb]
  apply (isPreconnected_univ.prod isPreconnected_Ioo).image N.coordinate_map
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, ha.trans_lt hz.2.1, hz.2.2.trans_le hb⟩



theorem mem_central_sphere_iff_of_mem {x : M} (hx : x ∈ N.carrier) :
    x ∈ N.central_sphere ↔ (N.coordinate_inverse x).2 = 0 := by
  rw [N.central_sphere_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    have h0 : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
    rw [N.coordinate_inverse_coordinate_map_of_axial_mem (by simpa only [hz0] using h0)]
    exact hz0
  · intro hz
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hz⟩,
      N.coordinate_map_coordinate_inverse hx⟩



theorem exists_centered_region_subset_open {O : Set M} (hO : IsOpen O)
    (hSO : N.central_sphere ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ r ≤ N.epsilon⁻¹ ∧ N.region (-r) r ⊆ O := by
  let W := (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∩ N.coordinate_map ⁻¹' O
  have hW : IsOpen W := N.coordinate_map_smooth.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod isOpen_Ioo) hO
  have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hSW : (univ : Set UnitTwoSphere) ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨q, s⟩ ⟨_, hs⟩
    have hs0 : s = 0 := hs
    subst s
    refine ⟨⟨mem_univ _, neg_neg_of_pos he, he⟩, hSO ?_⟩
    rw [N.central_sphere_eq]
    exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  obtain ⟨u, v, _, hv, hu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hW hSW
  obtain ⟨δ, hδ, hδv⟩ := Metric.isOpen_iff.mp hv 0 (h0v rfl)
  let r := min (δ / 2) (N.epsilon⁻¹ / 2)
  have hr : 0 < r := lt_min (half_pos hδ) (half_pos he)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨r, hr, (min_le_right _ _).trans (half_le_self he.le), ?_⟩
  intro x hx
  have hball : (N.coordinate_inverse x).2 ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_lt_neg hrδ).trans hx.2.1, hx.2.2.trans hrδ⟩
  have hxO := (huv ⟨hu (mem_univ _), hδv hball⟩).2
  change N.coordinate_map (N.coordinate_inverse x) ∈ O at hxO
  rwa [N.coordinate_map_coordinate_inverse hx.1] at hxO



theorem isCompact_image_closed_axial_interval {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    IsCompact (N.coordinate_map '' (univ ×ˢ Icc a b)) := by
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  exact ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩



theorem image_closed_axial_interval_subset_carrier {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    N.coordinate_map '' (univ ×ˢ Icc a b) ⊆ N.carrier := by
  rintro _ ⟨z, hz, rfl⟩
  exact N.coordinate_map_mem_of_axial_mem ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)


theorem boundary_subset_closed_core : N.boundary_sphere ⊆ N.closed_core := by
  rw [← N.core_frontier_eq_boundary]
  exact frontier_subset_closure.trans N.closed_core_compact.isClosed.closure_subset



theorem core_disjoint_end_neck : Disjoint N.core N.end_neck.carrier := by
  apply Set.disjoint_left.mpr
  intro x hx he
  have hy : x ∈ N.closed_core := interior_subset (N.core_eq_interior_closed_core ▸ hx)
  rw [N.closed_core_eq_complement_end] at hy
  exact hy.2 he



theorem boundary_subset_inner_end_closure {b : ℝ} (hb : -N.epsilon⁻¹ < b) :
    N.boundary_sphere ⊆ closure (N.end_neck.region (-N.epsilon⁻¹) b) := by
  by_cases hhalf : -N.epsilon⁻¹ / 2 ≤ b
  · apply N.boundary_subset_negative_end_closure.trans
    apply closure_mono
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.trans_le hhalf⟩
  have hblow : -N.end_neck.epsilon⁻¹ < b := by rwa [N.end_neck_epsilon]
  have hhigh : -N.epsilon⁻¹ / 2 < N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon]
    have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
    linarith
  let K := N.end_neck.coordinate_map '' (univ ×ˢ Icc b (-N.epsilon⁻¹ / 2))
  have hK : IsCompact K := N.end_neck.isCompact_image_closed_axial_interval hblow hhigh
  have hKend : K ⊆ N.end_neck.carrier :=
    N.end_neck.image_closed_axial_interval_subset_carrier hblow hhigh
  have hsplit : N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ⊆
      N.end_neck.region (-N.epsilon⁻¹) b ∪ K := by
    intro x hx
    by_cases hxb : (N.end_neck.coordinate_inverse x).2 < b
    · exact Or.inl ⟨hx.1, hx.2.1, hxb⟩
    · apply Or.inr
      refine ⟨N.end_neck.coordinate_inverse x, ⟨mem_univ _, le_of_not_gt hxb, hx.2.2.le⟩,
        N.end_neck.coordinate_map_coordinate_inverse hx.1⟩
  intro x hx
  have hxsplit := closure_mono hsplit (N.boundary_subset_negative_end_closure hx)
  rw [closure_union, hK.isClosed.closure_eq] at hxsplit
  rcases hxsplit with hxinner | hxK
  · exact hxinner
  · have hxcore := N.boundary_subset_closed_core hx
    rw [N.closed_core_eq_complement_end] at hxcore
    exact False.elim (hxcore.2 (hKend hxK))

end PoincareConjecture.CapCertificate
