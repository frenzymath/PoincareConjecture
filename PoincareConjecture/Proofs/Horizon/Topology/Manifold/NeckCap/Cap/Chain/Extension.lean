import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Maximal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Frontier.Append

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

open BalancedNeckChain

theorem exists_outgoing_chain_extension_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ ε₀ →
        ∀ C ∈ H.caps, ∀ T : BalancedNeckChain g C.epsilon,
          C.IsOutgoingChain H T →
          ∀ P ∈ H.necks, P.center ∈ H.X \ C.carrier →
          ∀ b ∈ T.shape.active, b + 1 ∉ T.shape.active →
            P.center ∈ closure ((T.neck b).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) →
            P.center ∉ T.unionOpen →
            ∃ D : BalancedNeckChain g C.epsilon,
              T.IsExtension D ∧ C.IsOutgoingChain H D ∧ b + 1 ∈ D.shape.active := by
  obtain ⟨ε₁, hε₁, -, hoverlap⟩ := EpsilonNeck.exists_frontier_reversal_balanced_overlap.{u}
  obtain ⟨ε₂, hε₂, hsmall, happend⟩ := exists_append_at_outer_frontier_threshold.{u}
  obtain ⟨ε₃, hε₃, -, hcapture⟩ :=
    EpsilonNeck.exists_positive_quarter_subset_frontier_neck_inner_slab_threshold.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    ((min_le_right _ _).trans (min_le_left _ _)).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε C hC T hT P hP hPX b hb hnext hfront hout
  have hεC := (H.cap_epsilon C hC).trans_le hε
  have hεb := T.epsilon_eq b hb
  have hεP : P.epsilon = C.epsilon :=
    (H.neck_epsilon P hP).trans (H.cap_epsilon C hC).symm
  have houtb : P.center ∉ (T.neck b).carrier := by
    intro hx
    exact hout (mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
  obtain ⟨Q, hsame, hpositive, hnegative, hwithin, -, hQsep⟩ :=
    hoverlap (T.neck b) P (hT.separating b hb)
      (hεb.trans_le (hεC.trans (min_le_left _ _))) (hεP.trans hεb.symm)
      (by simpa only [hεb] using hfront) houtb
  have hεQ : Q.epsilon = C.epsilon := hsame.epsilon_eq.trans hεP
  have hQfront : Q.center ∈ closure ((T.neck b).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by
    rwa [hsame.center_eq]
  have hQout : Q.center ∉ T.unionOpen := by rwa [hsame.center_eq]
  obtain ⟨D, hshape, hext, hsource, hnew, -⟩ :=
    happend T Q P (hεC.trans ((min_le_right _ _).trans (min_le_left _ _))) hεQ hsame
      hT.separating b hb hnext hQfront hQout
      (by simpa only [hεb] using hpositive) (by simpa only [hεb] using hnegative)
      (by simpa only [hεb] using hwithin)
  have hactive : D.shape.active = insert (b + 1) T.shape.active := by
    rw [hshape, ChainShape.extendRight_active hb hnext]
  have hD : C.IsOutgoingChain H D := by
    refine ⟨hext.1 hT.zero_active, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hactive, mem_insert_iff] at hj
      rcases hj with rfl | hj
      · have := hT.nonnegative b hb
        omega
      · exact hT.nonnegative j hj
    · rw [← hext.2.2 0 hT.zero_active]
      exact hT.first_neck
    · rw [hsource]
      exact insert_subset (mem_insert_of_mem _ hP) hT.source_necks
    · intro j hj hjpos
      rw [hactive, mem_insert_iff] at hj
      rcases hj with rfl | hj
      · rwa [hnew, hsame.center_eq]
      · rw [← hext.2.2 j hj]
        exact hT.centers j hj hjpos
    · intro j hj
      rw [hactive, mem_insert_iff] at hj
      rcases hj with rfl | hj
      · rwa [hnew]
      · rw [← hext.2.2 j hj]
        exact hT.separating j hj
    · apply hT.quarter_capture.of_append hext hb hnext hshape
      rw [hnew]
      have hslab := hcapture (T.neck b) Q
        (hεb.trans_le (hεC.trans ((min_le_right _ _).trans (min_le_right _ _))))
        (hεQ.trans hεb.symm) (by simpa only [hεb] using hQfront)
      intro x hx
      exact hslab (by simpa only [hεb] using hx)
  exact ⟨D, hext, hD, hactive.symm ▸ mem_insert (b + 1) T.shape.active⟩

end PoincareConjecture.CapCertificate
