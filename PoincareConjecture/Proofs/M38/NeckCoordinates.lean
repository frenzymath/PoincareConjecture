import PoincareConjecture.Proofs.M38.EventBoundary








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}


theorem neck_coordinate_mem (N : EpsilonNeck g) {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_map z ∈ N.carrier := by
  have h := (N.coordinate (z.1, ⟨z.2, hz.2⟩)).property
  rwa [N.coordinate_map_eq] at h


theorem neck_coordinate_inverse_map (N : EpsilonNeck g) {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_inverse (N.coordinate_map z) = z := by
  have h := N.coordinate_inverse_left (z.1, ⟨z.2, hz.2⟩)
  simpa only [N.coordinate_map_eq] using h


theorem neck_coordinate_map_inverse (N : EpsilonNeck g) {x : M}
    (hx : x ∈ N.carrier) : N.coordinate_map (N.coordinate_inverse x) = x := by
  have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
  simpa only [N.coordinate_map_eq] using h


theorem neck_unit_domain (N : EpsilonNeck g) :
    (Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (-1 : ℝ) 1 ⊆
      Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have hwidth : 1 < N.epsilon⁻¹ := (one_lt_inv₀ N.epsilon_pos).mpr (by
    linarith [N.epsilon_lt_half])
  intro z hz
  exact ⟨Set.mem_univ _, (neg_lt_neg hwidth).trans hz.2.1, hz.2.2.trans hwidth⟩



theorem neck_coordinate_image_open (N : EpsilonNeck g)
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (hsub : U ⊆ Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    IsOpen (N.coordinate_map '' U) := by
  let lift : NeckDomain N.epsilon → RoundCylinderSpace := fun z => (z.1, z.2.1)
  have hlift : Continuous lift :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hmap : IsOpenMap (fun z : NeckDomain N.epsilon => (N.coordinate z).1) :=
    N.carrier_open.isOpenMap_subtype_val.comp N.coordinate.isOpenMap
  have heq : N.coordinate_map '' U =
      (fun z : NeckDomain N.epsilon => (N.coordinate z).1) '' (lift ⁻¹' U) := by
    apply Set.Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact ⟨(z.1, ⟨z.2, (hsub hz).2⟩), hz, N.coordinate_map_eq _⟩
    · rintro x ⟨z, hz, rfl⟩
      exact ⟨lift z, hz, (N.coordinate_map_eq z).symm⟩
  rw [heq]
  exact hmap _ (hU.preimage hlift)

end PoincareConjecture.M38
