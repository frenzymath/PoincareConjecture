import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Frontier.Append
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Frontier.Prepend
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Frontier.Selection











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NeckOnlyCover

theorem exists_covering_balanced_chain :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (H : NeckOnlyCover g), H.epsilon ≤ ε₀ →
        (∀ N ∈ H.necks, N.IsSeparating) →
        ∃ C : BalancedNeckChain g H.epsilon,
          C.IsSelectedFrom H ∧ C.HasQuarterCapture ∧ H.X ⊆ C.unionOpen := by
  obtain ⟨ε₁, hε₁, hsmall, hfrontier⟩ := exists_neck_at_outer_end_of_quarter_capture.{u}
  obtain ⟨ε₂, hε₂, _, happend⟩ := exists_positive_frontier_extension.{u}
  obtain ⟨ε₃, hε₃, _, hprepend⟩ := exists_selected_prepend_threshold.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans (hsmall.trans (by norm_num)), ?_⟩
  intro M _ _ _ _ _ _ _ g H hε hsep
  have hbounds : H.epsilon ≤ ε₁ ∧ H.epsilon ≤ ε₂ ∧ H.epsilon ≤ ε₃ := by
    simpa only [le_min_iff] using hε
  obtain ⟨C, hselected, hcapture, hmax⟩ := H.exists_maximal_selected_chain
  refine ⟨C, hselected, hcapture, ?_⟩
  by_contra hmiss
  obtain ⟨P, hP, hPx, hfront, _, a, ha, hend, _, _⟩ :=
    hfrontier H hbounds.1 C hselected.2 hcapture hmiss
  have hout : P.center ∉ C.unionOpen := (C.unionOpen.isOpen.frontier_eq ▸ hfront).2
  rcases hend with ⟨hprev, hnegative⟩ | ⟨hnext, hpositive⟩
  · obtain ⟨D, hext, hDs, hDc, hnew⟩ := hprepend H hbounds.2.2 C hselected hcapture
      hsep P hP hPx a ha hprev hnegative hout
    exact hprev ((hmax D hDs hDc hext).1 hnew)
  · obtain ⟨D, hext, hDs, hDc, hnew⟩ := happend H hbounds.2.1 hsep C hselected hcapture
      P hP hPx a ha hnext hpositive hout
    exact hnext ((hmax D hDs hDc hext).1 hnew)

end PoincareConjecture.NeckOnlyCover
