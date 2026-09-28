import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.ConnectedNeckCapCover

theorem exists_outgoing_chain_with_cap_frontier_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε₀ →
        ∀ C ∈ H.caps, ∃ T : BalancedNeckChain g C.epsilon,
          C.IsOutgoingChain H T ∧
          ∀ x ∈ H.X ∩ frontier (C.carrier ∪ (T.unionOpen : Set M)),
            ∃ D ∈ H.caps, x ∈ D.core := by
  obtain ⟨ε₁, hε₁, hsmall, hmaximal⟩ :=
    CapCertificate.exists_maximal_outgoing_chain_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hfrontier⟩ :=
    CapCertificate.exists_chain_frontier_positive_end_threshold.{u}
  obtain ⟨ε₃, hε₃, -, hextend⟩ :=
    CapCertificate.exists_outgoing_chain_extension_threshold.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε C hC
  obtain ⟨T, hT, hmax⟩ := hmaximal H (hε.trans (min_le_left _ _)) C hC
  refine ⟨T, hT, ?_⟩
  intro x hx
  rcases H.pointwise_cover x hx.1 with ⟨P, hP, hcenter⟩ | hcap
  · obtain ⟨b, hb, hnext, hpositive⟩ := hfrontier C
      ((H.cap_epsilon C hC).trans_le
        (hε.trans ((min_le_right _ _).trans (min_le_left _ _))))
      T hT.zero_active hT.nonnegative hT.first_neck hT.quarter_capture x hx.2
    have hout : x ∉ C.carrier ∪ (T.unionOpen : Set M) :=
      ((C.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hx.2).2
    have hPX : P.center ∈ H.X \ C.carrier := by
      rw [hcenter]
      exact ⟨hx.1, fun h => hout (Or.inl h)⟩
    obtain ⟨S, hext, hS, hnew⟩ := hextend H
      (hε.trans ((min_le_right _ _).trans (min_le_right _ _))) C hC T hT
      P hP hPX b hb hnext (hcenter.symm ▸ hpositive)
      (by rw [hcenter]; exact fun h => hout (Or.inr h))
    exact False.elim (hnext ((hmax S hS hext).1 hnew))
  · exact hcap

theorem exists_outgoing_chain_cover_or_cap_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε₀ →
        ∀ C ∈ H.caps, (H.X ∩ C.carrier).Nonempty →
          ∃ T : BalancedNeckChain g C.epsilon, C.IsOutgoingChain H T ∧
            (H.X ⊆ C.carrier ∪ (T.unionOpen : Set M) ∨
              ∃ x ∈ H.X ∩ frontier (C.carrier ∪ (T.unionOpen : Set M)),
                ∃ D ∈ H.caps, x ∈ D.core) := by
  obtain ⟨ε₀, hε₀, hsmall, hchain⟩ := exists_outgoing_chain_with_cap_frontier_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε C hC hmeet
  obtain ⟨T, hT, hfront⟩ := hchain H hε C hC
  refine ⟨T, hT, ?_⟩
  by_cases hX : H.X ⊆ C.carrier ∪ (T.unionOpen : Set M)
  · exact Or.inl hX
  · right
    have hcontact : (H.X ∩ frontier (C.carrier ∪ (T.unionOpen : Set M))).Nonempty := by
      by_contra hnot
      have hdisj := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnot)
      have hopen := C.carrier_open.union T.unionOpen.isOpen
      have hmeet' : (H.X ∩ interior (C.carrier ∪ (T.unionOpen : Set M))).Nonempty := by
        rw [hopen.interior_eq]
        obtain ⟨x, hx, hxC⟩ := hmeet
        exact ⟨x, hx, Or.inl hxC⟩
      exact hX ((Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
        H.connected_X.isPreconnected hdisj hmeet').trans interior_subset)
    obtain ⟨x, hx⟩ := hcontact
    exact ⟨x, hx, hfront x hx⟩

end PoincareConjecture.ConnectedNeckCapCover
