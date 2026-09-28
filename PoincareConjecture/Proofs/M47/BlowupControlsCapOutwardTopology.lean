import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRecutFrontier

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem cap_outward_core_eq_complement {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    closure (N.recutCarrier b) = N.carrier \ N.end_neck.region b N.epsilon⁻¹ := by
  rw [closure_eq_self_union_frontier, N.recutCarrier_frontier_eq_axial_sphere hb hb']
  ext x
  constructor
  · rintro (hx | ⟨z, hz, rfl⟩)
    · refine ⟨N.recutCarrier_subset_carrier b hx, ?_⟩
      intro he
      rcases hx with hx | hx
      · rw [N.closed_core_eq_complement_end] at hx
        exact hx.2 he.1
      · exact (not_lt_of_ge hx.2.2.le) he.2.1
    · have hzB : z.2 = b := hz.2
      have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
        simpa only [hzB, N.end_neck_epsilon, mem_Ioo] using And.intro hb hb'
      refine ⟨N.end_neck_subset (N.end_neck.coordinate_map_mem_of_axial_mem hzN), ?_⟩
      intro he
      have hlt := he.2.1
      rw [N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem hzN, hzB] at hlt
      exact (lt_irrefl b) hlt
  · rintro ⟨hx, hnot⟩
    by_cases he : x ∈ N.end_neck.carrier
    · have hz := (N.end_neck.coordinate_inverse_mem x he).2
      rw [N.end_neck_epsilon] at hz
      have hle : (N.end_neck.coordinate_inverse x).2 ≤ b :=
        le_of_not_gt (fun h => hnot ⟨he, h, hz.2⟩)
      rcases hle.lt_or_eq with hlt | heq
      · exact Or.inl (Or.inr ⟨he, hz.1, hlt⟩)
      · exact Or.inr ⟨N.end_neck.coordinate_inverse x, ⟨mem_univ _, heq⟩,
          N.end_neck.coordinate_map_coordinate_inverse he⟩
    · exact Or.inl (Or.inl (N.closed_core_eq_complement_end ▸ ⟨hx, he⟩))

theorem cap_outward_sphere_subset_tail_closure {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    N.end_neck.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) ⊆
      closure (N.end_neck.region b N.epsilon⁻¹) := by
  rintro x ⟨z, hz, rfl⟩
  have hzB : z.2 = b := hz.2
  have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    simpa only [hzB, N.end_neck_epsilon, mem_Ioo] using And.intro hb hb'
  have hzcl : z ∈ closure (univ ×ˢ Ioo b N.epsilon⁻¹) := by
    rw [closure_prod_eq, closure_univ, closure_Ioo hb'.ne]
    exact ⟨mem_univ _, by rw [hzB]; exact ⟨le_rfl, hb'.le⟩⟩
  have hcont := N.end_neck.coordinate_map_smooth.continuousOn.continuousAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzN⟩)
  have hcl := hcont.continuousWithinAt.mem_closure_image hzcl
  rw [← N.end_neck.region_eq_image
    (by simpa only [N.end_neck_epsilon] using hb.le) (by rw [N.end_neck_epsilon])] at hcl
  exact hcl

theorem cap_outward_core_interior {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    interior (closure (N.recutCarrier b)) = N.recutCarrier b := by
  apply Subset.antisymm
  · intro x hx
    have hxcl := interior_subset hx
    rw [closure_eq_self_union_frontier,
      N.recutCarrier_frontier_eq_axial_sphere hb hb'] at hxcl
    rcases hxcl with hxV | hxS
    · exact hxV
    · have hxTail := cap_outward_sphere_subset_tail_closure N hb hb' hxS
      obtain ⟨y, hy, hytail⟩ := mem_closure_iff.mp hxTail _ isOpen_interior hx
      have hyK := interior_subset hy
      rw [cap_outward_core_eq_complement N hb hb'] at hyK
      exact (hyK.2 hytail).elim
  · exact interior_maximal subset_closure (N.recutCarrier_isOpen hb hb')

theorem cap_outward_core_frontier {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    frontier (closure (N.recutCarrier b)) =
      N.end_neck.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) := by
  rw [frontier, closure_closure, cap_outward_core_interior N hb hb']
  have h := N.recutCarrier_frontier_eq_axial_sphere hb hb'
  rwa [frontier, (N.recutCarrier_isOpen hb hb').interior_eq] at h

theorem cap_outward_core_geometry {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    IsCompact (closure (N.recutCarrier b)) ∧
      closure (N.recutCarrier b) ⊆ N.carrier ∧
      N.core ⊆ interior (closure (N.recutCarrier b)) := by
  have hcompact := N.recutCarrier_compact_closure hb hb'
  refine ⟨hcompact.1, hcompact.2, ?_⟩
  rw [cap_outward_core_interior N hb hb']
  exact fun _ hx => Or.inl (interior_subset (N.core_eq_interior_closed_core ▸ hx))

end PoincareConjecture.M47
