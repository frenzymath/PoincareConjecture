import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.Separation.HornNecks

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NeckOnlyCover

open BalancedNeckChain

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem exists_maximal_selected_chain_extending (H : NeckOnlyCover g)
    (C₀ : BalancedNeckChain g H.epsilon) (hC₀ : C₀.IsSelectedFrom H)
    (hc₀ : C₀.HasQuarterCapture) :
    ∃ C : BalancedNeckChain g H.epsilon,
      C.IsSelectedFrom H ∧ C.HasQuarterCapture ∧ C₀.IsExtension C ∧
      ∀ D : BalancedNeckChain g H.epsilon,
        D.IsSelectedFrom H → D.HasQuarterCapture → C.IsExtension D → D.IsExtension C := by
  classical
  let A := {C : BalancedNeckChain g H.epsilon //
    C.IsSelectedFrom H ∧ C.HasQuarterCapture ∧ C₀.IsExtension C}
  have : Nonempty A := ⟨⟨C₀, hC₀, hc₀, IsExtension.refl C₀⟩⟩
  let r : A → A → Prop := fun C D => C.1.IsExtension D.1
  have hbound (s : Set A) (hs : IsChain r s) (hne : s.Nonempty) :
      ∃ L : A, ∀ C ∈ s, r C L := by
    let : Nonempty s := hne.to_subtype
    have hdir : Directed IsExtension (fun C : s => C.1.1) := by
      intro C D
      by_cases he : C.1 = D.1
      · refine ⟨D, ?_, IsExtension.refl _⟩
        simpa only [he] using IsExtension.refl D.1.1
      · rcases hs C.2 D.2 he with hCD | hDC
        · exact ⟨D, hCD, IsExtension.refl _⟩
        · exact ⟨C, IsExtension.refl _, hDC⟩
    obtain ⟨L, hLs, hLc, hL⟩ := exists_directed_limit_selected H
      (fun C : s => C.1.1) hdir (fun C => C.1.2.1) (fun C => C.1.2.2.1)
    obtain ⟨D, hD⟩ := hne
    have hC₀L : C₀.IsExtension L := D.2.2.2.trans (hL ⟨D, hD⟩)
    exact ⟨⟨L, hLs, hLc, hC₀L⟩, fun C hC => hL ⟨C, hC⟩⟩
  obtain ⟨C, hC⟩ := exists_maximal_of_nonempty_chains_bounded hbound
    (fun hCD hDE => IsExtension.trans hCD hDE)
  refine ⟨C.1, C.2.1, C.2.2.1, C.2.2.2, ?_⟩
  intro D hDs hDc hCD
  exact hC ⟨D, hDs, hDc, C.2.2.2.trans hCD⟩ hCD

theorem exists_covering_balanced_chain_extending :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (H : NeckOnlyCover g), H.epsilon ≤ ε₀ →
        (∀ N ∈ H.necks, N.IsSeparating) →
        ∀ C₀ : BalancedNeckChain g H.epsilon,
          C₀.IsSelectedFrom H → C₀.HasQuarterCapture →
          ∃ C : BalancedNeckChain g H.epsilon,
            C.IsSelectedFrom H ∧ C.HasQuarterCapture ∧ C₀.IsExtension C ∧
              H.X ⊆ C.unionOpen := by
  obtain ⟨ε₁, hε₁, hsmall, hfrontier⟩ := exists_neck_at_outer_end_of_quarter_capture.{u}
  obtain ⟨ε₂, hε₂, _, happend⟩ := exists_positive_frontier_extension.{u}
  obtain ⟨ε₃, hε₃, _, hprepend⟩ := exists_selected_prepend_threshold.{u}
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃),
    (min_le_left _ _).trans (hsmall.trans (by norm_num)), ?_⟩
  intro M _ _ _ _ _ _ _ g H hε hsep C₀ hC₀ hc₀
  have hb : H.epsilon ≤ ε₁ ∧ H.epsilon ≤ ε₂ ∧ H.epsilon ≤ ε₃ := by
    simpa only [le_min_iff] using hε
  obtain ⟨C, hselected, hcapture, hext, hmax⟩ :=
    H.exists_maximal_selected_chain_extending C₀ hC₀ hc₀
  refine ⟨C, hselected, hcapture, hext, ?_⟩
  by_contra hmiss
  obtain ⟨P, hP, hPx, hfront, _, a, ha, hend, _, _⟩ :=
    hfrontier H hb.1 C hselected.2 hcapture hmiss
  have hout : P.center ∉ C.unionOpen := (C.unionOpen.isOpen.frontier_eq ▸ hfront).2
  rcases hend with ⟨hprev, hnegative⟩ | ⟨hnext, hpositive⟩
  · obtain ⟨D, hCD, hDs, hDc, hnew⟩ := hprepend H hb.2.2 C hselected hcapture
      hsep P hP hPx a ha hprev hnegative hout
    exact hprev ((hmax D hDs hDc hCD).1 hnew)
  · obtain ⟨D, hCD, hDs, hDc, hnew⟩ := happend H hb.2.1 hsep C hselected hcapture
      P hP hPx a ha hnext hpositive hout
    exact hnext ((hmax D hDs hDc hCD).1 hnew)

end PoincareConjecture.NeckOnlyCover

namespace PoincareConjecture.StrongHorn

theorem exists_anchored_covering_chain :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T ε : ℝ}
        (E : GeneralizedFlowExtension F T),
        ∀ (A : RepairedNeckCapTopologyTheory.{u}) (hεpos : 0 < ε)
          (_hε : ε ≤ ε₀) (hA : ε ≤ A.epsilon₀) (horn : StrongHorn E ε)
          (N : TerminalStrongNeck E ε), N.center ∈ horn.carrier →
          ∃ (hhalf : ε < 1 / 2) (C : BalancedNeckChain (E.extended.metric T) ε),
            C.IsSelectedFrom (horn.neckOnlyCover A hεpos hA) ∧
            C.HasQuarterCapture ∧ 0 ∈ C.shape.active ∧
            C.neck 0 = N.spatialNeck hhalf ∧ horn.carrier ⊆ C.unionOpen := by
  obtain ⟨ε₁, hε₁, hsmall, hsep⟩ := exists_boundary_sphere_transport.{u}
  obtain ⟨ε₂, hε₂, _, hchain⟩ :=
    NeckOnlyCover.exists_covering_balanced_chain_extending.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro F T ε E A hεpos hε hA horn N hN
  have hhalf : ε < 1 / 2 :=
    (hε.trans ((min_le_left _ _).trans hsmall)).trans_lt (by norm_num)
  let H := horn.neckOnlyCover A hεpos hA
  let P := N.spatialNeck hhalf
  let C₀ := BalancedNeckChain.singleton P
  have hselected : C₀.IsSelectedFrom H := by
    constructor
    · intro Q hQ
      change Q ∈ ({P} : Set (EpsilonNeck (E.extended.metric T))) at hQ
      rw [mem_singleton_iff.mp hQ]
      exact ⟨rfl, hN⟩
    · intro i _
      exact hN
  have hcapture : C₀.HasQuarterCapture := by
    intro i hi hj
    change i ∈ Icc (0 : ℤ) 0 at hi
    change i + 1 ∈ Icc (0 : ℤ) 0 at hj
    obtain ⟨hil, hiu⟩ := hi
    obtain ⟨hjl, hju⟩ := hj
    omega
  have hseparating : ∀ Q ∈ H.necks, Q.IsSeparating := by
    intro Q hQ
    obtain ⟨_, _, _, _, _, h⟩ := hsep E hεpos (hε.trans (min_le_left _ _))
      horn Q hQ.1 hQ.2
    exact h
  obtain ⟨C, hCs, hCc, hC₀, hcover⟩ :=
    hchain H (hε.trans (min_le_right _ _)) hseparating C₀ hselected hcapture
  have hzero : (0 : ℤ) ∈ C₀.shape.active := ⟨le_rfl, le_rfl⟩
  exact ⟨hhalf, C, hCs, hCc, hC₀.1 hzero, (hC₀.2.2 0 hzero).symm, hcover⟩

end PoincareConjecture.StrongHorn
