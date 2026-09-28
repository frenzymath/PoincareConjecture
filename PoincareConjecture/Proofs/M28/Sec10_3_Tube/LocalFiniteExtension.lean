import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalBandPartition
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalCoordinatePrefix
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalSliceIsotopy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem exists_prefix_neck_extension_with_transition_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier →
        A.carrier ∩ B.carrier ⊆
          A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
            B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2) →
        ∀ b s : ℝ,
        b ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
        s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ →
        b < -A.epsilon⁻¹ / 2 → s < -B.epsilon⁻¹ / 2 →
        ∀ (U : Opens M) (L K S : Set M), A.carrier ⊆ U →
        ∀ (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
          (T₀ : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞),
        (∀ p : RoundCylinderSpace, 0 < p.2 → (F p : M) = T₀ p) →
        (∀ p : RoundCylinderSpace, b < (A.coordinate_inverse (T₀ p)).2 ↔ 0 < p.2) →
        IsCompact K →
        frontier K ⊆ S ∪ range (fun q : UnitTwoSphere => A.coordinate_map (q, b)) →
        (U : Set M) = (L ∪ K) ∪ A.region b A.epsilon⁻¹ →
        Disjoint B.carrier S → Disjoint B.carrier L →
        Disjoint (A.region b A.epsilon⁻¹) K →
        ∀ r : ℝ, 0 < r →
        (∀ q t, t ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
          b - r < t → t ≤ b → A.coordinate_map (q, t) ∈ K) →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(U ⊔ B.carrierOpen) ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace B.carrierOpen ∞)
          (K' : Set M) (r' : ℝ)
          (E : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞),
          0 < r' ∧ IsCompact K' ∧
          (frontier K' ⊆ S ∪ range (fun q : UnitTwoSphere => B.coordinate_map (q, s))) ∧
          ((U ⊔ B.carrierOpen : Opens M) : Set M) = (L ∪ K') ∪ B.region s B.epsilon⁻¹ ∧
          Disjoint (B.region s B.epsilon⁻¹) K' ∧
          (∀ q t, t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ →
            s - r' < t → t ≤ s → B.coordinate_map (q, t) ∈ K') ∧
          (∀ p : RoundCylinderSpace, 0 < p.2 → (D p : M) = T p) ∧
          (∀ p : RoundCylinderSpace, s < (B.coordinate_inverse (T p)).2 ↔ 0 < p.2) ∧
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (D (E.symm p) : M) = F p) ∧
          (∀ p : RoundCylinderSpace, p.2 ≤ 0 → (E.symm p).2 < 0) ∧
          Disjoint (U : Set M) (B.region (B.epsilon⁻¹ / 2) B.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, hsmall, hgraph⟩ := exists_sphereSlice_graph_and_isotopy_m28.{u}
  obtain ⟨ε₂, hε₂, _, hcharts⟩ := exists_prefix_cylinder_with_retained_half_m28.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB hneg hwithin b s hb hs hbq hsq
    U L K S hAU F T₀ hFtail hT₀side hK hfront hdecomp havoid havoidL hupper r hr hcollar
  have hc (q : UnitTwoSphere) : B.coordinate_map (q, s) ∈ A.carrier := by
    have hz : (q, s) ∈ B.cylinderDomain := ⟨mem_univ _, hs⟩
    apply hneg
    refine ⟨B.coordinate_map_mem hz, ?_⟩
    rw [B.coordinate_inverse_coordinate_map hz]
    exact ⟨hs.1, hsq⟩
  obtain ⟨f, hf, hdom, hrange, _⟩ := hgraph A B
    (hA.trans (min_le_left _ _)) (hB.trans (min_le_left _ _)) hs hc
  obtain ⟨hside, _, _⟩ := A.graph_half_partition_m28 B f hf.continuous hdom hs hsq hrange
    hneg hwithin
  obtain ⟨hbf, hK', hfront', hdecomp', hupper', hcut, hsep, r', hr', hcollar'⟩ :=
    A.extend_prefix_partition_m28 B f hf.continuous hdom hb hs hbq hsq hrange hneg hwithin
      U L K S hAU hK hfront hdecomp havoid havoidL hupper r hr hcollar
  obtain ⟨D, T, E, hDtail, hTside, hretain, _, hEstrict, _⟩ := hcharts A B
    (hA.trans (min_le_right _ _)) (hB.trans (min_le_right _ _)) s hs hc f hf hdom
      hrange.symm hside U F T₀ b hbf hFtail hT₀side hcut hsep
  have havoidPrefix : Disjoint (U : Set M) (B.region (B.epsilon⁻¹ / 2) B.epsilon⁻¹) := by
    apply disjoint_left.mpr
    intro x hxU hxB
    rw [hdecomp] at hxU
    rcases hxU with (hxL | hxK) | hxA
    · exact disjoint_left.mp havoidL hxB.1 hxL
    · apply disjoint_left.mp hupper' (Or.inl hxK)
      refine ⟨hxB.1, ?_, hxB.2.2⟩
      have hi := inv_pos.mpr B.epsilon_pos
      linarith [hxB.2.1]
    · exact (not_lt_of_ge (hwithin ⟨hxA.1, hxB.1⟩).2.2.2.le) hxB.2.1
  refine ⟨D, T, K ∪ A.closedGraphSlab_m28 (fun _ => b) f, r', E, hr', hK', hfront',
    hdecomp', hupper'.symm, ?_, hDtail, hTside, hretain, hEstrict, havoidPrefix⟩
  intro q t ht hlow hhigh
  have hz : (q, t) ∈ B.cylinderDomain := ⟨mem_univ _, ht⟩
  apply hcollar' _ (B.coordinate_map_mem hz)
  · simpa only [B.coordinate_inverse_coordinate_map hz] using hlow
  · simpa only [B.coordinate_inverse_coordinate_map hz] using hhigh



theorem exists_prefix_neck_extension_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (A B : EpsilonNeck g),
        A.epsilon ≤ ε₀ → B.epsilon ≤ ε₀ →
        B.region (-B.epsilon⁻¹) (-B.epsilon⁻¹ / 2) ⊆ A.carrier →
        A.carrier ∩ B.carrier ⊆
          A.region (-A.epsilon⁻¹ / 2) A.epsilon⁻¹ ∩
            B.region (-B.epsilon⁻¹) (B.epsilon⁻¹ / 2) →
        ∀ b s : ℝ,
        b ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
        s ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ →
        b < -A.epsilon⁻¹ / 2 → s < -B.epsilon⁻¹ / 2 →
        ∀ (U : Opens M) (L K S : Set M), A.carrier ⊆ U →
        ∀ (F : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace U ∞)
          (T₀ : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrierOpen ∞),
        (∀ p : RoundCylinderSpace, 0 < p.2 → (F p : M) = T₀ p) →
        (∀ p : RoundCylinderSpace, b < (A.coordinate_inverse (T₀ p)).2 ↔ 0 < p.2) →
        IsCompact K →
        frontier K ⊆ S ∪ range (fun q : UnitTwoSphere => A.coordinate_map (q, b)) →
        (U : Set M) = (L ∪ K) ∪ A.region b A.epsilon⁻¹ →
        Disjoint B.carrier S → Disjoint B.carrier L →
        Disjoint (A.region b A.epsilon⁻¹) K →
        ∀ r : ℝ, 0 < r →
        (∀ q t, t ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
          b - r < t → t ≤ b → A.coordinate_map (q, t) ∈ K) →
        ∃ (D : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace ↥(U ⊔ B.carrierOpen) ∞)
          (T : Diffeomorph CylModel (𝓡 3) RoundCylinderSpace B.carrierOpen ∞)
          (K' : Set M) (r' : ℝ),
          0 < r' ∧ IsCompact K' ∧
          (frontier K' ⊆ S ∪ range (fun q : UnitTwoSphere => B.coordinate_map (q, s))) ∧
          ((U ⊔ B.carrierOpen : Opens M) : Set M) = (L ∪ K') ∪ B.region s B.epsilon⁻¹ ∧
          Disjoint (B.region s B.epsilon⁻¹) K' ∧
          (∀ q t, t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ →
            s - r' < t → t ≤ s → B.coordinate_map (q, t) ∈ K') ∧
          (∀ p : RoundCylinderSpace, 0 < p.2 → (D p : M) = T p) ∧
          (∀ p : RoundCylinderSpace, s < (B.coordinate_inverse (T p)).2 ↔ 0 < p.2) := by
  obtain ⟨ε₀, hε₀, hsmall, h⟩ := exists_prefix_neck_extension_with_transition_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g A B hA hB hneg hwithin b s hb hs hbq hsq
    U L K S hAU F T₀ hFtail hT₀side hK hfront hdecomp havoid havoidL hupper r hr hcollar
  obtain ⟨D, T, K', r', _, hr', hK', hfront', hdecomp', hupper', hcollar', htail, hside, _⟩ :=
    h A B hA hB hneg hwithin b s hb hs hbq hsq U L K S hAU F T₀ hFtail hT₀side
      hK hfront hdecomp havoid havoidL hupper r hr hcollar
  exact ⟨D, T, K', r', hr', hK', hfront', hdecomp', hupper', hcollar', htail, hside⟩

end PoincareConjecture.EpsilonNeck
