import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CompactCapSideOrder

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CappedTubeCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_chain_neck_confinement (T : CappedTubeCertificate g)
    (i j : ℤ) (hi : i ∈ T.tube.chain.shape.active) (hj : j ∈ T.tube.chain.shape.active)
    (hdisj : Disjoint (T.tube.chain.neck i).carrier (T.tube.chain.neck j).carrier)
    (hcap : Disjoint T.cap.carrier (T.tube.chain.neck i).carrier ∨
      Disjoint T.cap.carrier (T.tube.chain.neck j).carrier) :
    let N : Bool → EpsilonNeck g := fun b => T.tube.chain.neck (if b then j else i)
    ∃ K : Set M, IsCompact K ∧ K ⊆ T.carrier ∧
      ∀ γ : ℝ → M, γ 0 = (N false).center → γ 1 = (N true).center →
        ContinuousOn γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) T.carrier →
        ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
          ∃ (k : Bool) (c d : ℝ), 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
            γ c ∈ (N k).central_sphere ∧ γ d ∈ (N k).central_sphere ∧
            γ t ∉ (N k).region (-((N k).epsilon⁻¹ / 2)) ((N k).epsilon⁻¹ / 2) := by
  obtain ⟨k, C, hC, _, hCU, hcenter₀, hcenter₁, _, hfront⟩ :=
    T.exists_compact_side_containing_chain_centers i j hi hj hdisj hcap
  let N := T.tube.chain.neck (if k then j else i)
  have hN : N.carrier ⊆ T.carrier := by
    apply Subset.trans _ T.tube_subset
    rw [T.tube.carrier_eq_chain_union]
    exact subset_iUnion_of_subset ⟨if k then j else i, by cases k <;> assumption⟩ Subset.rfl
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let D := N.coordinate_map '' (univ ×ˢ Icc (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2))
  have hD : IsCompact D := N.isCompact_coordinate_slab_intrinsic (by linarith) (by linarith)
  have hDN : D ⊆ N.carrier := N.coordinate_slab_subset_carrier_m28 (by linarith) (by linarith)
  have hmiddle : N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2) ⊆ D := by
    intro x hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  let K := C ∪ D
  refine ⟨K, hC.union hD, union_subset hCU (hDN.trans hN), ?_⟩
  intro γ hγ₀ hγ₁ hγ _hγU t ht htK
  have htC : γ t ∉ C := fun hx => htK (Or.inl hx)
  have h₀C : γ 0 ∈ C := by
    rw [hγ₀]
    exact hcenter₀
  have h₁C : γ 1 ∈ C := by
    rw [hγ₁]
    exact hcenter₁
  obtain ⟨c, hc, hcf⟩ := (hγ.mono (Icc_subset_Icc le_rfl ht.2)).exists_frontier_crossing_before
    hC.isClosed ht.1 h₀C htC
  obtain ⟨d, hd, hdf⟩ := (hγ.mono (Icc_subset_Icc ht.1 le_rfl)).exists_frontier_crossing_after
    hC.isClosed ht.2 htC h₁C
  refine ⟨k, c, d, hc.1, hc.2.le, hd.1.le, hd.2, hfront hcf, hfront hdf, ?_⟩
  exact fun hx => htK (Or.inr (hmiddle hx))

end PoincareConjecture.CappedTubeCertificate
