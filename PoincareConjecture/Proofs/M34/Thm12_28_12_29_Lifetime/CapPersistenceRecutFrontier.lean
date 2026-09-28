import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceRecutCompact










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)



theorem boundary_eq_recut_end_frontier {b : ℝ} (hb : -N.epsilon⁻¹ < b) :
    N.boundary_sphere = N.recutCarrier b ∩
      frontier (N.end_neck.region (-N.epsilon⁻¹) b) := by
  ext x
  constructor
  · intro hx
    have hy := N.boundary_subset_closed_core hx
    refine ⟨Or.inl hy, N.boundary_subset_inner_end_closure hb hx, ?_⟩
    rw [(N.end_neck.region_isOpen _ _).interior_eq]
    intro he
    rw [N.closed_core_eq_complement_end] at hy
    exact hy.2 he.1
  · rintro ⟨hx, hxf⟩
    have hnot : x ∉ N.end_neck.region (-N.epsilon⁻¹) b := by
      simpa only [(N.end_neck.region_isOpen _ _).interior_eq] using hxf.2
    have hy : x ∈ N.closed_core := hx.resolve_right hnot
    rw [N.closed_core_eq_complement_end] at hy
    rw [N.boundary_eq_end_frontier]
    refine ⟨hy.1, closure_mono (fun _ h => h.1) hxf.1, ?_⟩
    simpa only [N.end_neck.carrier_open.interior_eq] using hy.2




theorem recutCarrier_frontier_subset_axial_sphere {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    frontier (N.recutCarrier b) ⊆
      N.end_neck.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) := by
  intro x hx
  have hxV := (N.recutCarrier_compact_closure hb hb').2 hx.1
  have hnot : x ∉ N.recutCarrier b := by
    simpa only [(N.recutCarrier_isOpen hb hb').interior_eq] using hx.2
  have he : x ∈ N.end_neck.carrier := by
    by_contra he
    apply hnot
    exact Or.inl (N.closed_core_eq_complement_end ▸ ⟨hxV, he⟩)
  have ht : (N.end_neck.coordinate_inverse x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [N.end_neck_epsilon] using (N.end_neck.coordinate_inverse_mem x he).2
  have hlow : b ≤ (N.end_neck.coordinate_inverse x).2 := by
    exact le_of_not_gt (fun hlt => hnot (Or.inr ⟨he, ht.1, hlt⟩))
  have hupp : (N.end_neck.coordinate_inverse x).2 ≤ b := by
    by_contra hle
    have hxO : x ∈ N.end_neck.region b N.epsilon⁻¹ := ⟨he, lt_of_not_ge hle, ht.2⟩
    obtain ⟨y, hyO, hyR⟩ := mem_closure_iff.mp hx.1
      (N.end_neck.region b N.epsilon⁻¹) (N.end_neck.region_isOpen _ _) hxO
    rcases hyR with hyY | hyE
    · rw [N.closed_core_eq_complement_end] at hyY
      exact hyY.2 hyO.1
    · exact (not_lt_of_ge hyE.2.2.le) hyO.2.1
  exact ⟨N.end_neck.coordinate_inverse x, ⟨mem_univ _, le_antisymm hupp hlow⟩,
    N.end_neck.coordinate_map_coordinate_inverse he⟩



theorem recutCarrier_frontier_eq_axial_sphere {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    frontier (N.recutCarrier b) =
      N.end_neck.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) := by
  apply Subset.antisymm (N.recutCarrier_frontier_subset_axial_sphere hb hb')
  rintro x ⟨z, hz, rfl⟩
  have hzB : z.2 = b := hz.2
  have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    simpa only [hzB, N.end_neck_epsilon, mem_Ioo] using And.intro hb hb'
  have he := N.end_neck.coordinate_map_mem_of_axial_mem (z := z) hzN
  have hinv := N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem (z := z) hzN
  have hzcl : z ∈ closure (univ ×ˢ Ioo (-N.epsilon⁻¹) b) := by
    rw [closure_prod_eq, closure_univ, closure_Ioo hb.ne]
    exact ⟨mem_univ _, by rw [hzB]; exact ⟨hb.le, le_rfl⟩⟩
  have hcont := N.end_neck.coordinate_map_smooth.continuousOn.continuousAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzN⟩)
  have hcl := hcont.continuousWithinAt.mem_closure_image hzcl
  rw [← N.end_neck.region_eq_image
    (by rw [N.end_neck_epsilon]) (by simpa only [N.end_neck_epsilon] using hb'.le)] at hcl
  refine ⟨closure_mono (fun _ h => Or.inr h) hcl, ?_⟩
  rw [(N.recutCarrier_isOpen hb hb').interior_eq]
  intro hx
  rcases hx with hxY | hxE
  · rw [N.closed_core_eq_complement_end] at hxY
    exact hxY.2 he
  · have hlt := hxE.2.2
    rw [hinv, hzB] at hlt
    exact (lt_irrefl b) hlt

end PoincareConjecture.CapCertificate
