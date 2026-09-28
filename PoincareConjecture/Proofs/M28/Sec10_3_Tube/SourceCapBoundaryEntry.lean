import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundaryAnchoredEntry
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizerAnchors











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck




theorem exists_source_anchored_entry_below_cap_graph_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N₀ ∈ S.cover.necks, ∀ P ∈ S.cover.necks,
        ∀ (N W : EpsilonNeck (E.flow.metric E.time)),
          (N = N₀ ∨ N = N₀.reversed) →
        ∀ tN ∈ Icc S.lower S.upper, ∀ tW ∈ Icc S.lower S.upper, tN < tW →
          SourceEdgeCommonOrientationPacket N P W (γ := S.path) tN tW →
          SourceEdgePacket N W epsilon →
        ∀ f : UnitTwoSphere → ℝ, (∀ p, |f p| < 7 * W.epsilon⁻¹ / 8) →
          ∃ t₁ ∈ Ioo (0 : ℝ) tN,
            (E.flow.metric E.time).pathELength S.path t₁ tN =
              ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) ∧
            MapsTo S.path (Icc t₁ tN) N.carrier ∧ S.path t₁ ∉ W.carrier ∧
            ∃ v ∈ Ico t₁ tW, MapsTo S.path (Icc v tW) W.carrier ∧
              neckGraphHeight W f (S.path v) < 0 := by
  obtain ⟨epsilonA, hApos, hAsmall, hA⟩ :=
    exists_source_minimizer_anchors_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hR⟩ := exists_source_neck_region_accuracy.{u}
  refine ⟨min epsilonA epsilonR, lt_min hApos hRpos,
    (min_le_left _ _).trans hAsmall, ?_⟩
  intro epsilon C A D₀ D E S hbase hsmall N₀ hN₀ P hP N W hchoice
    tN htN tW htW hNW H J f hfb
  have hNscale : N.scale = N₀.scale := by
    rcases hchoice with h | h <;> simp only [h, reversed_scale]
  have hcN₀ : S.path tN = N₀.center := by
    have h := H.center_N
    rcases hchoice with hchoice | hchoice <;>
      simpa only [hchoice, reversed_center] using h
  obtain ⟨t₁, ht₁, _, _, hanchor₀, _⟩ := hA E S hbase
    (hsmall.trans (min_le_left _ _)) N₀ hN₀ tN htN hcN₀
  have hanchor : (E.flow.metric E.time).pathELength S.path t₁ tN =
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) := by
    simpa only [hNscale, J.epsilon_N, S.cover.neck_epsilon N₀ hN₀,
      S.cover_epsilon] using hanchor₀
  have hregion := (hR E S hbase
    (hsmall.trans (min_le_right _ _))).2.1
  have hWU : W.carrier ⊆ S.source_region.carrier := by
    have hPU : P.carrier ⊆ S.source_region.carrier :=
      fun _ hx => hregion ⟨P, hP, hx⟩
    rcases H.choice with h | h <;> simpa only [h, reversed_carrier] using hPU
  have hε : N.epsilon ≤ 1 / 1000 := by
    rw [J.epsilon_N]
    exact (hsmall.trans (min_le_left _ _)).trans hAsmall
  have hentry := H.exists_anchored_entry_below_cap_graph J hε hWU ht₁.1.le
    ht₁.2 hNW (htW.2.trans S.upper_lt_one.le) S.path_smooth
    S.source_region.path_mem S.source_region.finite_length
    S.source_region.minimizing hanchor hfb
  exact ⟨t₁, ht₁, hanchor, hentry⟩

end PoincareConjecture.M28
