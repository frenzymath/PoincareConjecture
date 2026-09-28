import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeCommonOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizerAnchors
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizerSubsegments
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceEdgeMinimizerOverlapAssembly
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceBalancedChainAssembly









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck





theorem exists_source_minimizer_edge_packet_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N₀ ∈ S.cover.necks, ∀ P ∈ S.cover.necks,
        ∀ tN ∈ Icc S.lower S.upper, ∀ tP ∈ Icc S.lower S.upper, tN < tP →
          S.path tN = N₀.center → S.path tP = P.center →
          MapsTo S.path (Ico tN tP) N₀.carrier → P.center ∈ frontier N₀.carrier →
          ∃ N Q : EpsilonNeck (E.flow.metric E.time),
            (N = N₀ ∨ N = N₀.reversed) ∧
            SourceEdgeCommonOrientationPacket N P Q (γ := S.path) tN tP ∧
            SourceEdgePacket N Q epsilon := by
  obtain ⟨epsilonA, hApos, _, hA⟩ := exists_source_minimizer_anchors_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hR⟩ := exists_source_neck_region_accuracy.{u}
  obtain ⟨epsilonO, hOpos, hOsmall, hO⟩ :=
    exists_source_edge_common_orientation_packet.{u}
  let epsilon₀ := min epsilonO (min epsilonA epsilonR)
  refine ⟨epsilon₀, lt_min hOpos (lt_min hApos hRpos),
    (min_le_left _ _).trans hOsmall, ?_⟩
  intro epsilon C A D₀ D E S hbase hsmall N₀ hN₀ P hP tN htN tP htP hNP
    hcN hcP hedge hfront
  let g := E.flow.metric E.time
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : (E.flow.slice E.time).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hεN₀ : N₀.epsilon = epsilon :=
    (S.cover.neck_epsilon N₀ hN₀).trans S.cover_epsilon
  have hεP : P.epsilon = epsilon :=
    (S.cover.neck_epsilon P hP).trans S.cover_epsilon
  have h0N : 0 < tN := S.lower_pos.trans_le htN.1
  have hP1 : tP < 1 := htP.2.trans_lt S.upper_lt_one
  have hsmallA : epsilon ≤ epsilonA :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨N, Q, hchoice, H⟩ := hO N₀ P
    (by rw [hεN₀]; exact hsmall.trans (min_le_left _ _))
    (hεP.trans hεN₀.symm) hNP
    (S.path_smooth.mono (Icc_subset_Icc h0N.le hP1.le)) hcN hcP hedge hfront
  have hNε : N.epsilon = epsilon := by
    rcases hchoice with rfl | rfl <;> simpa only [reversed_epsilon] using hεN₀
  have hNscale : N.scale = N₀.scale := by
    rcases hchoice with rfl | rfl <;> simp only [reversed_scale]
  have hNcarrier : N.carrier = N₀.carrier := by
    rcases hchoice with rfl | rfl <;> simp only [reversed_carrier]
  have hQscale : Q.scale = P.scale := by
    rcases H.choice with h | h <;> simp only [h, reversed_scale]
  have hQcarrier : Q.carrier = P.carrier := by
    rcases H.choice with h | h <;> simp only [h, reversed_carrier]
  obtain ⟨t₁, ht₁, _, _, hanchor₁, _⟩ :=
    hA E S hbase hsmallA N₀ hN₀ tN htN hcN
  obtain ⟨_, _, t₂, ht₂, _, hanchor₂⟩ :=
    hA E S hbase hsmallA P hP tP htP hcP
  have hregion := (hR E S hbase
    (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))).2.1
  have hNU : N.carrier ⊆ S.source_region.carrier := by
    rw [hNcarrier]
    exact fun _ hx => hregion ⟨N₀, hN₀, hx⟩
  have hQU : Q.carrier ⊆ S.source_region.carrier := by
    rw [hQcarrier]
    exact fun _ hx => hregion ⟨P, hP, hx⟩
  have hε : N.epsilon ≤ 1 / 1000 := by
    rw [hNε]
    exact (hsmall.trans ((min_le_left _ _).trans hOsmall)).trans (by norm_num)
  have hmin (a b : ℝ) (ha : t₁ ≤ a) (hab : a ≤ b) (hb : b ≤ t₂) :
      g.pathELength S.path a b =
        intrinsicEDist g S.source_region.carrier (S.path a) (S.path b) :=
    pathELength_eq_intrinsicEDist_subsegment g (ht₁.1.le.trans ha) hab
      (hb.trans ht₂.2.le) S.path_smooth S.source_region.path_mem
      S.source_region.finite_length S.source_region.minimizing
  have hadd (a b c : ℝ) (_ha : t₁ ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
      (_hc : c ≤ t₂) : g.pathELength S.path a c =
        g.pathELength S.path a b + g.pathELength S.path b c :=
    (Manifold.pathELength_add hab hbc).symm
  have htransition : Q.center ∈ frontier N.carrier →
      ∃ σ : ℝ, σ = 1 ∧ ∃ v ∈ Ioo tN tP,
        σ * (N.coordinate_inverse (S.path v)).2 =
          (509 : ℝ) * N.epsilon⁻¹ / 512 ∧
        (∀ t ∈ Ioo v tP, (509 : ℝ) * N.epsilon⁻¹ / 512 <
          σ * (N.coordinate_inverse (S.path t)).2) ∧
        neckSignedRegion N σ ((127 : ℝ) * N.epsilon⁻¹ / 128)
          N.epsilon⁻¹ ⊆ Q.carrier := by
    intro _
    obtain ⟨v, hv, hlevel, hafter, htail⟩ := H.transition
    exact ⟨1, rfl, v, hv, by simpa only [one_mul] using hlevel,
      by simpa only [one_mul] using hafter,
      by simpa only [neckSignedRegion_one] using htail⟩
  have hwithin := source_edge_whole_overlap_of_minimizer_anchors N Q hε
    H.epsilon_eq H.scale H.narrow_closure
    (N.carrier_open.frontier_eq ▸ H.frontier).2 H.forward_region H.reciprocal_region
    H.anchor_band htransition hNU hQU ht₁.2 hNP ht₂.1
    (S.path_smooth.mono (Icc_subset_Icc ht₁.1.le ht₂.2.le))
    (S.source_region.path_mem.mono (Icc_subset_Icc ht₁.1.le ht₂.2.le) (Subset.refl _))
    H.center_N H.center_Q H.edge hmin hadd
    (by simpa only [hNscale, hNε, hεN₀] using hanchor₁)
    (by simpa only [hQscale, hNε, hεP] using hanchor₂)
  have hrecip : Q.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) ⊆ N.carrier := by
    have h := H.reciprocal_region.trans (N.region_subset_carrier _ _)
    simpa only [hNε] using h
  refine ⟨N, Q, hchoice, H, ?_⟩
  exact ⟨hNε, H.epsilon_eq.trans hNε,
    by simpa only [hNε] using H.forward_carrier,
    hrecip, H.overlap,
    ⟨by simpa only [hNε] using H.forward_carrier, hrecip⟩,
    by simpa only [hNε] using hwithin,
    by simpa only [hNε] using H.center_distance⟩

end PoincareConjecture.M28
