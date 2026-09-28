import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereCrossings











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonTubeCertificate

open M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {X : Set M}




theorem exists_chain_neck_confinement (T : EpsilonTubeCertificate g X)
    (i j : ℤ) (hi : i ∈ T.chain.shape.active) (hj : j ∈ T.chain.shape.active)
    (hdisj : Disjoint (T.chain.neck i).carrier (T.chain.neck j).carrier) :
    let N : Bool → EpsilonNeck g := fun b => T.chain.neck (if b then j else i)
    ∃ K : Set M, IsCompact K ∧ K ⊆ T.carrier ∧
      ∀ γ : ℝ → M, γ 0 ∈ (N false).central_sphere → γ 1 ∈ (N true).central_sphere →
        ContinuousOn γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) T.carrier →
        ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
          ∃ (k : Bool) (c d : ℝ), 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
            γ c ∈ (N k).central_sphere ∧ γ d ∈ (N k).central_sphere ∧
            γ t ∉ (N k).region (-((N k).epsilon⁻¹ / 2)) ((N k).epsilon⁻¹ / 2) := by
  let U : TopologicalSpace.Opens M := ⟨T.carrier, T.carrier_open⟩
  let N₀ := T.chain.neck i
  let N₁ := T.chain.neck j
  have hN₀ : N₀.carrier ⊆ T.carrier := by
    rw [T.carrier_eq_chain_union]
    exact subset_iUnion_of_subset ⟨i, hi⟩ Subset.rfl
  have hN₁ : N₁.carrier ⊆ T.carrier := by
    rw [T.carrier_eq_chain_union]
    exact subset_iUnion_of_subset ⟨j, hj⟩ Subset.rfl
  have hSdisj : Disjoint N₀.central_sphere N₁.central_sphere :=
    hdisj.mono N₀.central_sphere_subset N₁.central_sphere_subset
  obtain ⟨h₀, h₁, a, b, ha, _, _, hb, hc₀, hc₁, hz₀, hz₁,
      hlow, hhigh, horder⟩ := T.cylinder.exists_ordered_isotopic_sphere_heights
    (U := U) (T.central_sphere_isotopy i hi) (T.central_sphere_isotopy j hj) hSdisj
  have horiented : ∃ f₀ f₁ : M → ℝ,
      ContinuousOn f₀ T.carrier ∧ ContinuousOn f₁ T.carrier ∧
      (∀ x ∈ T.carrier, f₀ x = 0 ↔ x ∈ N₀.central_sphere) ∧
      (∀ x ∈ T.carrier, f₁ x = 0 ↔ x ∈ N₁.central_sphere) ∧
      (∀ x ∈ N₁.central_sphere, 0 < f₀ x) ∧
      (∀ x ∈ N₀.central_sphere, f₁ x < 0) ∧
      ∀ x ∈ T.carrier, 0 ≤ f₀ x → f₁ x ≤ 0 →
        x ∈ T.cylinder.compactSlab a b := by
    rcases horder with horder | horder
    · refine ⟨h₀, h₁, hc₀, hc₁, hz₀, hz₁,
        fun x hx => horder.1 x (hN₁ (N₁.central_sphere_subset hx)) hx,
        fun x hx => horder.2 x (hN₀ (N₀.central_sphere_subset hx)) hx, ?_⟩
      intro x hx hf₀ hf₁
      apply (T.cylinder.mem_compactSlab_iff ha hb).mpr
      refine ⟨hx, ?_, ?_⟩
      · exact le_of_not_gt (fun h => (not_lt_of_ge hf₀) (hlow x hx h).1)
      · exact le_of_not_gt (fun h => (not_lt_of_ge hf₁) (hhigh x hx h).2)
    · refine ⟨fun x => -h₀ x, fun x => -h₁ x, hc₀.neg, hc₁.neg,
        fun x hx => by simpa only [neg_eq_zero] using hz₀ x hx,
        fun x hx => by simpa only [neg_eq_zero] using hz₁ x hx,
        fun x hx => neg_pos.mpr (horder.1 x (hN₁ (N₁.central_sphere_subset hx)) hx),
        fun x hx => neg_neg_of_pos (horder.2 x (hN₀ (N₀.central_sphere_subset hx)) hx), ?_⟩
      intro x hx hf₀ hf₁
      apply (T.cylinder.mem_compactSlab_iff ha hb).mpr
      refine ⟨hx, ?_, ?_⟩
      · apply le_of_not_gt
        intro h
        have hh := (hlow x hx h).2
        linarith
      · apply le_of_not_gt
        intro h
        have hh := (hhigh x hx h).1
        linarith
  obtain ⟨f₀, f₁, hf₀, hf₁, hzero₀, hzero₁, hother₀, hother₁, hcapture⟩ := horiented
  let Slab := T.cylinder.compactSlab a b
  have hSlab : IsCompact Slab := T.cylinder.isCompact_compactSlab ha hb
  have hSlabU : Slab ⊆ T.carrier := T.cylinder.compactSlab_subset ha hb
  let J := Slab ∩ f₀ ⁻¹' Ici (0 : ℝ)
  have hJclosed : IsClosed J :=
    (hf₀.mono hSlabU).preimage_isClosed_of_isClosed hSlab.isClosed isClosed_Ici
  have hJ : IsCompact J := hSlab.of_isClosed_subset hJclosed inter_subset_left
  have hJU : J ⊆ T.carrier := inter_subset_left.trans hSlabU
  let Middle := J ∩ f₁ ⁻¹' Iic (0 : ℝ)
  have hMiddleClosed : IsClosed Middle :=
    (hf₁.mono hJU).preimage_isClosed_of_isClosed hJclosed isClosed_Iic
  have hMiddle : IsCompact Middle := hJ.of_isClosed_subset hMiddleClosed inter_subset_left
  have hMiddleU : Middle ⊆ T.carrier := inter_subset_left.trans hJU
  have hmiddleCapture {x : M} (hx : x ∈ T.carrier) (hx₀ : 0 ≤ f₀ x) (hx₁ : f₁ x ≤ 0) :
      x ∈ Middle := ⟨⟨hcapture x hx hx₀ hx₁, hx₀⟩, hx₁⟩
  let D₀ := N₀.coordinate_map '' (univ ×ˢ Icc (-(N₀.epsilon⁻¹ / 2)) (N₀.epsilon⁻¹ / 2))
  let D₁ := N₁.coordinate_map '' (univ ×ˢ Icc (-(N₁.epsilon⁻¹ / 2)) (N₁.epsilon⁻¹ / 2))
  have hA₀ : 0 < N₀.epsilon⁻¹ := inv_pos.mpr N₀.epsilon_pos
  have hA₁ : 0 < N₁.epsilon⁻¹ := inv_pos.mpr N₁.epsilon_pos
  have hD₀ : IsCompact D₀ := N₀.isCompact_coordinate_slab_intrinsic (by linarith) (by linarith)
  have hD₁ : IsCompact D₁ := N₁.isCompact_coordinate_slab_intrinsic (by linarith) (by linarith)
  have hD₀U : D₀ ⊆ T.carrier :=
    (N₀.coordinate_slab_subset_carrier_m28 (by linarith) (by linarith)).trans hN₀
  have hD₁U : D₁ ⊆ T.carrier :=
    (N₁.coordinate_slab_subset_carrier_m28 (by linarith) (by linarith)).trans hN₁
  have hregion₀ : N₀.region (-(N₀.epsilon⁻¹ / 2)) (N₀.epsilon⁻¹ / 2) ⊆ D₀ := by
    intro x hx
    exact ⟨N₀.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N₀.coordinate_map_coordinate_inverse hx.1⟩
  have hregion₁ : N₁.region (-(N₁.epsilon⁻¹ / 2)) (N₁.epsilon⁻¹ / 2) ⊆ D₁ := by
    intro x hx
    exact ⟨N₁.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N₁.coordinate_map_coordinate_inverse hx.1⟩
  let K := (Middle ∪ D₀) ∪ D₁
  refine ⟨K, (hMiddle.union hD₀).union hD₁,
    union_subset (union_subset hMiddleU hD₀U) hD₁U, ?_⟩
  intro γ hγ₀ hγ₁ hγ hγU t ht htK
  have htMiddle : γ t ∉ Middle := fun hx => htK (Or.inl (Or.inl hx))
  have hexit₀ : γ t ∉ N₀.region (-(N₀.epsilon⁻¹ / 2)) (N₀.epsilon⁻¹ / 2) :=
    fun hx => htK (Or.inl (Or.inr (hregion₀ hx)))
  have hexit₁ : γ t ∉ N₁.region (-(N₁.epsilon⁻¹ / 2)) (N₁.epsilon⁻¹ / 2) :=
    fun hx => htK (Or.inr (hregion₁ hx))
  by_cases ht₀ : f₀ (γ t) < 0
  · obtain ⟨d, hd, hdsphere⟩ := exists_sphere_return_after_negative_height
      hf₀ hzero₀ ht.1 ht.2 hγ hγU ht₀ (hother₀ _ hγ₁)
    exact ⟨false, 0, d, le_rfl, ht.1, hd.1.le, hd.2.le, hγ₀, hdsphere, hexit₀⟩
  · have ht₁ : 0 < f₁ (γ t) := by
      by_contra h
      exact htMiddle (hmiddleCapture (hγU ht) (le_of_not_gt ht₀) (le_of_not_gt h))
    obtain ⟨c, hc, hcsphere⟩ := exists_sphere_hit_before_positive_height
      hf₁ hzero₁ ht.1 ht.2 hγ hγU (hother₁ _ hγ₀) ht₁
    exact ⟨true, c, 1, hc.1.le, hc.2.le, ht.2, le_rfl, hcsphere, hγ₁, hexit₁⟩

end PoincareConjecture.EpsilonTubeCertificate
