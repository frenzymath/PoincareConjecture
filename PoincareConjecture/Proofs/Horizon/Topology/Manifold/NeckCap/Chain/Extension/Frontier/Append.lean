import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Append
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.SuccessorThreeQuarter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Invariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NeckOnlyCover

open BalancedNeckChain

theorem exists_positive_frontier_extension :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ ε₀ →
        (∀ N ∈ H.necks, N.IsSeparating) →
        ∀ C : BalancedNeckChain g H.epsilon,
          C.IsSelectedFrom H → C.HasQuarterCapture →
          ∀ P ∈ H.necks, P.center ∈ H.X →
          ∀ b ∈ C.shape.active, b + 1 ∉ C.shape.active →
            P.center ∈ closure ((C.neck b).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) →
            P.center ∉ C.unionOpen →
            ∃ D : BalancedNeckChain g H.epsilon,
              C.IsExtension D ∧ D.IsSelectedFrom H ∧ D.HasQuarterCapture ∧
                b + 1 ∈ D.shape.active := by
  obtain ⟨ε₁, hε₁, _, hoverlap⟩ := EpsilonNeck.exists_frontier_reversal_balanced_overlap.{u}
  obtain ⟨ε₂, hε₂, hsmall, happend⟩ := exists_append_at_outer_frontier_threshold.{u}
  obtain ⟨ε₃, hε₃, _, hcapture⟩ :=
    EpsilonNeck.exists_positive_quarter_subset_frontier_neck_inner_slab_threshold.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε hsep C hselected hCcapture P hP hPX b hb hnext hfront hout
  have hεb := C.epsilon_eq b hb
  have hεP := H.neck_epsilon P hP
  have houtb : P.center ∉ (C.neck b).carrier := by
    intro hx
    exact hout (mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
  obtain ⟨Q, hsame, hpositive, hnegative, hwithin, _, _⟩ :=
    hoverlap (C.neck b) P (hselected.isSeparating hsep hb)
      (by simpa only [hεb] using hε.trans (min_le_left _ _)) (hεP.trans hεb.symm)
      (by simpa only [hεb] using hfront) houtb
  have hεQ : Q.epsilon = H.epsilon := hsame.epsilon_eq.trans hεP
  have hQfront : Q.center ∈ closure ((C.neck b).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) := by
    rwa [hsame.center_eq]
  have hQout : Q.center ∉ C.unionOpen := by rwa [hsame.center_eq]
  obtain ⟨D, hshape, hext, hsource, hnew, _⟩ :=
    happend C Q P (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) hεQ hsame
      (fun i hi => hselected.isSeparating hsep hi) b hb hnext hQfront hQout
      (by simpa only [hεb] using hpositive) (by simpa only [hεb] using hnegative)
      (by simpa only [hεb] using hwithin)
  have hactive : D.shape.active = insert (b + 1) C.shape.active := by
    rw [hshape, ChainShape.extendRight_active hb hnext]
  refine ⟨D, hext, hselected.of_insert hext hactive hsource hP ?_, ?_, ?_⟩
  · rw [hnew, hsame.center_eq]
    exact hPX
  · apply hCcapture.of_append hext hb hnext hshape
    rw [hnew]
    have hslab := hcapture (C.neck b) Q
      (by simpa only [hεb] using hε.trans ((min_le_right _ _).trans (min_le_right _ _)))
      (hεQ.trans hεb.symm) (by simpa only [hεb] using hQfront)
    intro x hx
    obtain ⟨z, hz, he⟩ := hslab (by simpa only [hεb] using hx)
    exact ⟨z, ⟨hz.1, hz.2⟩, he⟩
  · rw [hactive]
    exact Or.inl rfl

end PoincareConjecture.NeckOnlyCover
