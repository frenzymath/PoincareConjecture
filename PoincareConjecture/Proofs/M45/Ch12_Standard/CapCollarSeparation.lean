import PoincareConjecture.Proofs.M45.Ch12_Standard.CapNeckTopology









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



theorem neck_exists_collar_avoiding (N : EpsilonNeck g) {H : Set M}
    (hH : IsClosed H) (hNH : Disjoint N.central_sphere H) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ N.epsilon⁻¹ ∧
      N.region (-delta) delta ⊆ Hᶜ := by
  let D : Set RoundCylinderSpace := univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
  let W := D ∩ N.coordinate_map ⁻¹' Hᶜ
  have hW : IsOpen W := N.coordinate_map_smooth.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod isOpen_Ioo) hH.isOpen_compl
  have hpos := inv_pos.mpr N.epsilon_pos
  have hcentral : (univ ×ˢ ({0} : Set ℝ) : Set RoundCylinderSpace) ⊆ W := by
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    refine ⟨⟨mem_univ _, ?_⟩, ?_⟩
    · change -N.epsilon⁻¹ < z.2 ∧ z.2 < N.epsilon⁻¹
      rw [hz0]
      exact ⟨neg_lt_zero.mpr hpos, hpos⟩
    · apply Set.disjoint_left.mp hNH
      rw [N.central_sphere_eq]
      exact ⟨z, hz, rfl⟩
  obtain ⟨u, v, _hu, hv, hsu, htv, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hW hcentral
  obtain ⟨rho, hrho, hball⟩ :=
    Metric.mem_nhds_iff.mp (hv.mem_nhds (htv (mem_singleton 0)))
  refine ⟨min rho N.epsilon⁻¹, lt_min hrho hpos, min_le_right _ _, ?_⟩
  intro x hx
  have hzv : (N.coordinate_inverse x).2 ∈ v := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hx.2.1, min_le_left rho N.epsilon⁻¹],
      lt_of_lt_of_le hx.2.2 (min_le_left _ _)⟩
  have h := (huv ⟨hsu (mem_univ _), hzv⟩).2
  simpa only [mem_preimage, M36.neck_coordinate_inverse N hx.1] using h



theorem neck_middle_strip_compact (N : EpsilonNeck g) :
    IsCompact (N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))) := by
  have hpos := inv_pos.mpr N.epsilon_pos
  apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩



theorem neck_middle_strip_subset (N : EpsilonNeck g) :
    N.coordinate_map '' (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) ⊆
      N.carrier := by
  have hpos := inv_pos.mpr N.epsilon_pos
  rintro x ⟨z, hz, rfl⟩
  exact M36.neck_coordinate_mem N z
    ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩



theorem neck_outside_middle (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier)
    (hmid : x ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))) :
    x ∈ N.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) ∪
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
  have hz := (N.coordinate_inverse_mem x hx).2
  by_cases hneg : (N.coordinate_inverse x).2 < -N.epsilon⁻¹ / 2
  · exact Or.inl ⟨hx, hz.1, hneg⟩
  · apply Or.inr
    refine ⟨hx, ?_, hz.2⟩
    by_contra h
    apply hmid
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, le_of_not_gt hneg, le_of_not_gt h⟩,
      M36.neck_coordinate_inverse N hx⟩

end PoincareConjecture.M45
