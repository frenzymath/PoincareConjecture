import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.EndSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Maximal












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}



structure IsOutgoingChain (C : CapCertificate g) (H : ConnectedNeckCapCover g)
    (T : BalancedNeckChain g C.epsilon) : Prop where
  zero_active : 0 ∈ T.shape.active
  nonnegative : ∀ j ∈ T.shape.active, 0 ≤ j
  first_neck : T.neck 0 = C.end_neck
  source_necks : T.source_necks ⊆ insert C.end_neck H.necks
  centers : ∀ j ∈ T.shape.active, 0 < j → (T.neck j).center ∈ H.X \ C.carrier
  separating : ∀ j ∈ T.shape.active, (T.neck j).IsSeparating
  quarter_capture : T.HasQuarterCapture


theorem exists_singleton_outgoing_chain (C : CapCertificate g)
    (H : ConnectedNeckCapCover g) (hsep : C.end_neck.IsSeparating) :
    ∃ T : BalancedNeckChain g C.epsilon,
      C.IsOutgoingChain H T ∧ T.shape = .finite 0 0 := by
  have initial (ε : ℝ) (he : C.end_neck.epsilon = ε) :
      ∃ T : BalancedNeckChain g ε,
        T.shape = .finite 0 0 ∧ T.neck = (fun _ => C.end_neck) ∧
          T.source_necks = {C.end_neck} := by
    subst ε
    exact ⟨BalancedNeckChain.singleton C.end_neck, rfl, rfl, rfl⟩
  obtain ⟨T, hshape, hneck, hsource⟩ := initial C.epsilon C.end_neck_epsilon
  refine ⟨T, ?_, hshape⟩
  constructor
  · simp [hshape, ChainShape.active]
  · intro j hj
    simp only [hshape, ChainShape.active, mem_Icc] at hj
    exact hj.1
  · rw [hneck]
  · rw [hsource]
    exact singleton_subset_iff.mpr (mem_insert _ _)
  · intro j hj hjpos
    simp only [hshape, ChainShape.active, mem_Icc] at hj
    omega
  · intro j _
    simpa only [hneck] using hsep
  · intro j hj hjnext
    simp only [hshape, ChainShape.active, mem_Icc] at hj hjnext
    omega


theorem exists_directed_limit_outgoing {ι : Type*} [Nonempty ι]
    (C : CapCertificate g) (H : ConnectedNeckCapCover g)
    (T : ι → BalancedNeckChain g C.epsilon)
    (hdir : Directed BalancedNeckChain.IsExtension T)
    (houtgoing : ∀ n, C.IsOutgoingChain H (T n)) :
    ∃ L : BalancedNeckChain g C.epsilon,
      C.IsOutgoingChain H L ∧ ∀ n, (T n).IsExtension L := by
  classical
  obtain ⟨L, hactive, hsource, hext, _⟩ :=
    BalancedNeckChain.exists_directed_limit T hdir
  have hstage (j : ℤ) (hj : j ∈ L.shape.active) :
      ∃ n, j ∈ (T n).shape.active := by
    rw [hactive] at hj
    exact mem_iUnion.mp hj
  let n₀ : ι := Classical.choice inferInstance
  refine ⟨L, ?_, hext⟩
  constructor
  · exact (hext n₀).1 (houtgoing n₀).zero_active
  · intro j hj
    obtain ⟨n, hn⟩ := hstage j hj
    exact (houtgoing n).nonnegative j hn
  · rw [← (hext n₀).2.2 0 (houtgoing n₀).zero_active]
    exact (houtgoing n₀).first_neck
  · intro N hN
    rw [hsource] at hN
    obtain ⟨n, hn⟩ := mem_iUnion.mp hN
    exact (houtgoing n).source_necks hn
  · intro j hj hjpos
    obtain ⟨n, hn⟩ := hstage j hj
    rw [← (hext n).2.2 j hn]
    exact (houtgoing n).centers j hn hjpos
  · intro j hj
    obtain ⟨n, hn⟩ := hstage j hj
    rw [← (hext n).2.2 j hn]
    exact (houtgoing n).separating j hn
  · intro j hj hjnext
    obtain ⟨n, hn⟩ := hstage j hj
    obtain ⟨m, hm⟩ := hstage (j + 1) hjnext
    obtain ⟨p, hnp, hmp⟩ := hdir n m
    have hpj := hnp.1 hn
    have hpnext := hmp.1 hm
    rw [← (hext p).2.2 j hpj, ← (hext p).2.2 (j + 1) hpnext]
    exact (houtgoing p).quarter_capture j hpj hpnext


theorem exists_maximal_outgoing_chain (C : CapCertificate g)
    (H : ConnectedNeckCapCover g) (hsep : C.end_neck.IsSeparating) :
    ∃ T : BalancedNeckChain g C.epsilon,
      C.IsOutgoingChain H T ∧
      ∀ S : BalancedNeckChain g C.epsilon,
        C.IsOutgoingChain H S → T.IsExtension S → S.IsExtension T := by
  classical
  let A := {T : BalancedNeckChain g C.epsilon // C.IsOutgoingChain H T}
  have : Nonempty A := by
    obtain ⟨T, hT, _⟩ := C.exists_singleton_outgoing_chain H hsep
    exact ⟨⟨T, hT⟩⟩
  let r : A → A → Prop := fun T S => T.1.IsExtension S.1
  have hbound (s : Set A) (hs : IsChain r s) (hne : s.Nonempty) :
      ∃ L : A, ∀ T ∈ s, r T L := by
    let : Nonempty s := hne.to_subtype
    have hdir : Directed BalancedNeckChain.IsExtension (fun T : s => T.1.1) := by
      intro T S
      by_cases he : T.1 = S.1
      · refine ⟨S, ?_, BalancedNeckChain.IsExtension.refl _⟩
        simpa only [he] using BalancedNeckChain.IsExtension.refl S.1.1
      · rcases hs T.2 S.2 he with hTS | hST
        · exact ⟨S, hTS, BalancedNeckChain.IsExtension.refl _⟩
        · exact ⟨T, BalancedNeckChain.IsExtension.refl _, hST⟩
    obtain ⟨L, hL, hext⟩ := C.exists_directed_limit_outgoing H
      (fun T : s => T.1.1) hdir (fun T => T.1.2)
    exact ⟨⟨L, hL⟩, fun T hT => hext ⟨T, hT⟩⟩
  obtain ⟨T, hT⟩ := exists_maximal_of_nonempty_chains_bounded hbound
    (fun hTS hSU => BalancedNeckChain.IsExtension.trans hTS hSU)
  exact ⟨T.1, T.2, fun S hS hTS => hT ⟨S, hS⟩ hTS⟩



theorem exists_maximal_outgoing_chain_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ ε₀ →
        ∀ C : CapCertificate g, C ∈ H.caps →
          ∃ T : BalancedNeckChain g C.epsilon,
            C.IsOutgoingChain H T ∧
            ∀ S : BalancedNeckChain g C.epsilon,
              C.IsOutgoingChain H S → T.IsExtension S → S.IsExtension T := by
  obtain ⟨ε₁, hε₁, _, hsep⟩ := exists_end_neck_separating_threshold.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g H hH C hC
  exact C.exists_maximal_outgoing_chain H
    (hsep C ((H.cap_epsilon C hC).trans_le (hH.trans (min_le_left _ _))))

end PoincareConjecture.CapCertificate
