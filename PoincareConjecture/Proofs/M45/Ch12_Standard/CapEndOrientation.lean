import PoincareConjecture.Proofs.M45.Ch12_Standard.CapCollarSeparation









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.StandardCapNeighborhood

open M45

variable {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
  {F : MaximalStandardCapFlow g₀} {t epsilon C : ℝ} {x : StandardCapSpace}



theorem core_ne_univ (N : StandardCapNeighborhood atlas F t epsilon C x) :
    N.closed_core ≠ univ := by
  intro h
  have hx : N.end_neck.center ∈ N.closed_core := h.symm ▸ mem_univ _
  rw [N.closed_core_eq] at hx
  exact hx.2 (N.end_neck.toEpsilonNeck.central_sphere_subset
    N.end_neck.toEpsilonNeck.center_on_central_sphere)



theorem boundary_end_orientation
    (N : StandardCapNeighborhood atlas F t epsilon C x) :
    frontier N.closed_core ⊆ closure
      (N.end_neck.toEpsilonNeck.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) ∨
    frontier N.closed_core ⊆ closure
      (N.end_neck.toEpsilonNeck.region (epsilon⁻¹ / 2) epsilon⁻¹) := by
  let B := N.boundary_neck.toEpsilonNeck
  let E := N.end_neck.toEpsilonNeck
  let H := E.coordinate_map '' (univ ×ˢ Icc (-epsilon⁻¹ / 2) (epsilon⁻¹ / 2))
  have hK := N.core_compact.isClosed
  have hB : frontier N.closed_core = B.central_sphere := N.boundary_sphere
  have hH : IsCompact H := neck_middle_strip_compact E
  have hHE : H ⊆ E.carrier := neck_middle_strip_subset E
  have hBH : Disjoint B.central_sphere H := by
    apply Set.disjoint_left.mpr
    intro y hyB hyH
    have hyK : y ∈ N.closed_core :=
      hK.closure_eq ▸ frontier_subset_closure (hB.symm ▸ hyB)
    rw [N.closed_core_eq] at hyK
    exact hyK.2 (hHE hyH)
  obtain ⟨delta, hdelta, hdeltaE, havoid⟩ := neck_exists_collar_avoiding B hH.isClosed hBH
  have hside := neck_opposite_sides B hK ⟨x, N.center_in_core⟩ N.core_ne_univ hB
  obtain ⟨V, hVconn, hVthin, hVK, hBV⟩ :
      ∃ V : Set StandardCapSpace, IsPreconnected V ∧
        V ⊆ B.region (-delta) delta ∧ V ⊆ N.closed_coreᶜ ∧
        B.central_sphere ⊆ closure V := by
    rcases hside with hside | hside
    · refine ⟨B.region 0 delta, ?_, ?_, ?_, ?_⟩
      · exact (neckRegion_isConnected B (by linarith [B.epsilon_pos, inv_pos.mpr B.epsilon_pos])
          hdelta hdeltaE).isPreconnected
      · intro y hy
        exact ⟨hy.1, by linarith [hy.2.1], hy.2.2⟩
      · intro y hy
        exact hside.2 ⟨hy.1, hy.2.1, lt_of_lt_of_le hy.2.2 hdeltaE⟩
      · exact neckSphere_subset_closure_region B
          (by linarith [inv_pos.mpr B.epsilon_pos]) hdelta hdeltaE le_rfl hdelta.le
    · refine ⟨B.region (-delta) 0, ?_, ?_, ?_, ?_⟩
      · exact (neckRegion_isConnected B (by linarith) (neg_lt_zero.mpr hdelta)
          (inv_pos.mpr B.epsilon_pos).le).isPreconnected
      · intro y hy
        exact ⟨hy.1, hy.2.1, by linarith [hy.2.2]⟩
      · intro y hy
        exact hside.1 ⟨hy.1, by linarith [hy.2.1], hy.2.2⟩
      · exact neckSphere_subset_closure_region B (by linarith) (neg_lt_zero.mpr hdelta)
          (inv_pos.mpr B.epsilon_pos).le (neg_nonpos.mpr hdelta.le) le_rfl
  have hVE : V ⊆ E.carrier := by
    intro y hy
    by_contra h
    apply hVK hy
    rw [N.closed_core_eq]
    exact ⟨N.boundary_neck_subset (hVthin hy).1, h⟩
  have hcover : V ⊆ E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) ∪
      E.region (epsilon⁻¹ / 2) epsilon⁻¹ := by
    intro y hy
    exact neck_outside_middle E (hVE hy) (havoid (hVthin hy))
  have hdisjoint : Disjoint (E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2))
      (E.region (epsilon⁻¹ / 2) epsilon⁻¹) := by
    apply Set.disjoint_left.mpr
    intro y hy h'y
    have hpos := inv_pos.mpr N.epsilon_pos
    linarith [hy.2.2, h'y.2.1]
  rcases hVconn.subset_or_subset (M36.neck_region_isOpen E _ _)
    (M36.neck_region_isOpen E _ _) hdisjoint hcover with hleft | hright
  · exact Or.inl (hB ▸ hBV.trans (closure_mono hleft))
  · exact Or.inr (hB ▸ hBV.trans (closure_mono hright))

end PoincareConjecture.StandardCapNeighborhood
