import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.ContainedSphere

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem not_isCompact_of_half_region_subset (N : EpsilonNeck g) {K : Set M}
    (hK : K ⊆ N.carrier)
    (hhalf : N.region (-N.epsilon⁻¹) 0 ⊆ K ∨ N.region 0 N.epsilon⁻¹ ⊆ K) :
    ¬ IsCompact K := by
  intro hc
  let f : M → ℝ := fun x => (N.coordinate_inverse x).2
  have hclosed : IsClosed (f '' K) :=
    (hc.image_of_continuousOn (N.coordinate_inverse_smooth.continuousOn.snd.mono hK)).isClosed
  have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hrange {a b : ℝ} (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹)
      (hsub : N.region a b ⊆ K) : Ioo a b ⊆ f '' K := by
    intro t ht
    let q := (N.coordinate_inverse N.center).1
    let z : NeckDomain N.epsilon := (q, ⟨t, ha.trans_lt ht.1, ht.2.trans_le hb⟩)
    have hi := N.coordinate_inverse_left z
    refine ⟨N.coordinate z, hsub ⟨(N.coordinate z).property, ?_⟩, ?_⟩
    · rw [hi]
      exact ht
    · change (N.coordinate_inverse (N.coordinate z)).2 = t
      rw [hi]
  rcases hhalf with hn | hp
  · have hmem : -N.epsilon⁻¹ ∈ closure (Ioo (-N.epsilon⁻¹) (0 : ℝ)) := by
      rw [closure_Ioo (neg_ne_zero.mpr he.ne')]
      exact ⟨le_rfl, (neg_lt_zero.mpr he).le⟩
    obtain ⟨x, hx, heq⟩ := closure_minimal (hrange le_rfl he.le hn) hclosed hmem
    have hh := (N.coordinate_inverse_mem x (hK hx)).2.1
    change -N.epsilon⁻¹ < f x at hh
    rw [heq] at hh
    exact lt_irrefl _ hh
  · have hmem : N.epsilon⁻¹ ∈ closure (Ioo (0 : ℝ) N.epsilon⁻¹) := by
      rw [closure_Ioo he.ne]
      exact ⟨he.le, le_rfl⟩
    obtain ⟨x, hx, heq⟩ := closure_minimal (hrange (neg_nonpos.mpr he.le) le_rfl hp) hclosed hmem
    have hh := (N.coordinate_inverse_mem x (hK hx)).2.2
    change f x < N.epsilon⁻¹ at hh
    rw [heq] at hh
    exact lt_irrefl _ hh

theorem not_isCompact_of_frontier_eq_central_sphere (N : EpsilonNeck g) {K : Set M}
    (hK : K ⊆ N.carrier) (hfront : frontier K = N.central_sphere)
    (hint : (interior K).Nonempty) : ¬ IsCompact K := by
  intro hc
  have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hside {a b : ℝ} (ha : -N.epsilon⁻¹ ≤ a) (hb : b ≤ N.epsilon⁻¹)
      (hab : a < b) (hzero : b ≤ 0 ∨ 0 ≤ a) {x : M}
      (hx : x ∈ N.region a b) (hxK : x ∈ interior K) : N.region a b ⊆ K := by
    have havoid : Disjoint (N.region a b) (frontier K) := by
      rw [hfront]
      exact (N.central_sphere_disjoint_region a b hzero).symm
    have hcover : N.region a b ⊆ interior K ∪ Kᶜ := by
      intro y hy
      by_cases hky : y ∈ K
      · left
        by_contra hn
        exact disjoint_left.mp havoid hy ⟨hc.isClosed.closure_eq.symm ▸ hky, hn⟩
      · exact Or.inr hky
    rcases (N.isConnected_region ha hb hab).isPreconnected.subset_or_subset
      isOpen_interior hc.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover with h | h
    · exact h.trans interior_subset
    · exact False.elim (h hx (interior_subset hxK))
  obtain ⟨x, hx⟩ := hint
  rcases N.carrier_subset_region_union_central_union_region (hK (interior_subset hx)) with
    (hn | hs) | hp
  · exact N.not_isCompact_of_half_region_subset hK
      (Or.inl (hside le_rfl he.le (neg_lt_zero.mpr he) (Or.inl le_rfl) hn hx)) hc
  · exact (hfront.symm ▸ hs).2 hx
  · exact N.not_isCompact_of_half_region_subset hK
      (Or.inr (hside (neg_nonpos.mpr he.le) le_rfl he (Or.inr le_rfl) hp hx)) hc

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.CapCertificate

theorem exists_closed_core_neck_noncontainment_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (C : CapCertificate g) (N : EpsilonNeck g),
        C.epsilon = ε → N.epsilon = ε → ¬ C.closed_core ⊆ N.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := EpsilonNeck.exists_contained_compact_transport.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε C N hC hN hsub
  have hS : C.boundary_neck.central_sphere ⊆ N.carrier := by
    rw [← C.boundary_eq_neck_sphere]
    exact C.boundary_subset_closed_core.trans hsub
  obtain ⟨e, K, _, hK, hfix, _, hsphere⟩ :=
    htransport hεpos hε N C.boundary_neck hN (C.boundary_neck_epsilon.trans hC) hS
  have hcore : e.symm '' C.closed_core ⊆ N.carrier := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hout
    have h := hfix (e.symm x) (fun hy => hout (hK hy))
    rw [e.apply_symm_apply] at h
    exact hout (h ▸ hsub hx)
  have hfront : frontier (e.symm '' C.closed_core) = N.central_sphere := by
    rw [← e.symm.image_frontier, C.core_frontier_eq_boundary,
      C.boundary_eq_neck_sphere, ← hsphere]
    exact e.toEquiv.symm_image_image N.central_sphere
  have hint : (interior (e.symm '' C.closed_core)).Nonempty := by
    rw [← e.symm.image_interior, ← C.core_eq_interior_closed_core]
    exact C.core_nonempty.image e.symm
  exact N.not_isCompact_of_frontier_eq_central_sphere hcore hfront hint
    (C.closed_core_compact.image e.symm.continuous)

theorem exists_neck_noncontainment_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ (C : CapCertificate g) (N : EpsilonNeck g),
        C.epsilon = ε → N.epsilon = ε → ¬ C.carrier ⊆ N.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, hcore⟩ := exists_closed_core_neck_noncontainment_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g ε hεpos hε C N hC hN hsub
  exact hcore hεpos hε C N hC hN (C.closed_core_subset_carrier.trans hsub)

end PoincareConjecture.CapCertificate
