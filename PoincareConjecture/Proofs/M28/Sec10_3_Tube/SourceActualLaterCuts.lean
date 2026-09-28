import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizerCuts
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceBackwardAnchor
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizerAnchors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck

theorem exists_actual_later_negative_cut_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N₀ ∈ S.cover.necks, ∀ P₀ ∈ S.cover.necks,
        ∀ (N P Q R T V : EpsilonNeck (E.flow.metric E.time)),
          (N = N₀ ∨ N = N₀.reversed) → (P = P₀ ∨ P = P₀.reversed) →
        ∀ tN ∈ Icc S.lower S.upper, ∀ tP ∈ Icc S.lower S.upper,
        ∀ tQ tR : ℝ, tN < tQ → tQ < tR → tR ≤ tP →
          SourceEdgeCommonOrientationPacket N R Q (γ := S.path) tN tQ →
          SourceEdgeCommonOrientationPacket Q V T (γ := S.path) tQ tR →
          S.path tP = P.center →
          Disjoint P.carrier (N.region (-epsilon⁻¹) (-epsilon⁻¹ / 2)) := by
  obtain ⟨epsilonF, hFpos, hFsmall, hF⟩ := exists_later_negative_cut_accuracy.{u}
  obtain ⟨epsilonA, hApos, _, hA⟩ := exists_source_minimizer_anchors_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hR⟩ := exists_source_neck_region_accuracy.{u}
  let epsilon₀ := min epsilonF (min epsilonA epsilonR)
  refine ⟨epsilon₀, lt_min hFpos (lt_min hApos hRpos),
    (min_le_left _ _).trans hFsmall, ?_⟩
  intro epsilon C A D₀ D E S hbase hsmall N₀ hN₀ P₀ hP₀ N P Q R T V
    hNchoice hPchoice tN htN tP htP tQ tR hNQ hQR hRP H₀ H₁ hcP
  let g := E.flow.metric E.time
  have hNε : N.epsilon = epsilon := by
    have h := (S.cover.neck_epsilon N₀ hN₀).trans S.cover_epsilon
    rcases hNchoice with rfl | rfl <;> simpa only [reversed_epsilon] using h
  have hPε : P.epsilon = epsilon := by
    have h := (S.cover.neck_epsilon P₀ hP₀).trans S.cover_epsilon
    rcases hPchoice with rfl | rfl <;> simpa only [reversed_epsilon] using h
  have hNscale : N.scale = N₀.scale := by
    rcases hNchoice with rfl | rfl <;> simp only [reversed_scale]
  have hNcarrier : N.carrier = N₀.carrier := by
    rcases hNchoice with rfl | rfl <;> simp only [reversed_carrier]
  have hPcarrier : P.carrier = P₀.carrier := by
    rcases hPchoice with rfl | rfl <;> simp only [reversed_carrier]
  have hcN₀ : S.path tN = N₀.center := by
    have h := H₀.center_N
    rcases hNchoice with rfl | rfl <;> simpa only [reversed_center] using h
  obtain ⟨t₁, ht₁, _, _, hanchor₀, _⟩ := hA E S hbase
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) N₀ hN₀ tN htN hcN₀
  have hanchor : g.pathELength S.path t₁ tN =
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) := by
    simpa only [hNscale, hNε, S.cover.neck_epsilon N₀ hN₀, S.cover_epsilon]
      using hanchor₀
  have hregion := (hR E S hbase
    (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))).2.1
  have hNU : N.carrier ⊆ S.source_region.carrier := by
    rw [hNcarrier]
    exact fun _ hx => hregion ⟨N₀, hN₀, hx⟩
  have hPU : P.carrier ⊆ S.source_region.carrier := by
    rw [hPcarrier]
    exact fun _ hx => hregion ⟨P₀, hP₀, hx⟩
  have hNP : tN < tP := hNQ.trans (hQR.trans_le hRP)
  have hP1 : tP < 1 := htP.2.trans_lt S.upper_lt_one
  have hN0 : 0 < tN := S.lower_pos.trans_le htN.1
  have hεF : N.epsilon ≤ epsilonF := by
    rw [hNε]
    exact hsmall.trans (min_le_left _ _)
  obtain ⟨v, hv, hlevel, _, _⟩ := H₀.transition
  have hγN : MapsTo S.path (Icc tN v) N.carrier :=
    fun _ ht => H₀.edge ⟨ht.1, ht.2.trans_lt hv.2⟩
  have hsign := backward_anchor_height_le_of_positive_transition N
    (hεF.trans hFsmall) hNU ht₁.1.le ht₁.2 hv.1
    (hv.2.le.trans ((hQR.le.trans hRP).trans hP1.le))
    S.path_smooth S.source_region.path_mem S.source_region.finite_length
    S.source_region.minimizing H₀.center_N hγN hlevel hanchor
  have hfar := two_source_edges_pathELength_lower H₀ H₁ hNQ hQR hRP
    (S.path_smooth.mono (Icc_subset_Icc hN0.le hP1.le))
  have hcut := hF N P hεF (hPε.trans hNε.symm) hNU hPU ht₁.2 hNP
    (S.path_smooth.mono (Icc_subset_Icc ht₁.1.le hP1.le)) H₀.center_N hcP
    (fun a b ha hab hb => pathELength_eq_intrinsicEDist_subsegment g
      (ht₁.1.le.trans ha) hab (hb.trans hP1.le) S.path_smooth S.source_region.path_mem
      S.source_region.finite_length S.source_region.minimizing)
    hanchor (by simpa only [neg_mul] using hsign.2) hsign.1 hfar
  simpa only [hNε] using hcut

end PoincareConjecture.M28
