import PoincareConjecture.Proofs.M28.Mathlib.PathLengthAnchors
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28




theorem exists_source_minimizer_anchors_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N ∈ S.cover.necks, ∀ s ∈ Icc S.lower S.upper, S.path s = N.center →
          ∃ t₁ ∈ Ioo (0 : ℝ) s, ∃ t₂ ∈ Ioo s (1 : ℝ),
            (E.flow.metric E.time).pathELength S.path t₁ s =
              ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) ∧
            (E.flow.metric E.time).pathELength S.path s t₂ =
              ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) := by
  obtain ⟨epsilonE, hEpos, _, hexclude⟩ :=
    exists_source_neck_endpoint_exclusion_accuracy.{u}
  refine ⟨min epsilonE (1 / 1000), lt_min hEpos (by norm_num), min_le_right _ _, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall N hN s hs hcenter
  let g := E.flow.metric E.time
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : (E.flow.slice E.time).carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs0 : 0 < s := S.lower_pos.trans_le hs.1
  have hs1 : s < 1 := hs.2.trans_lt S.upper_lt_one
  have heps : N.epsilon ≤ 1 / 1000 := by
    rw [S.cover.neck_epsilon N hN, S.cover_epsilon]
    exact hsmall.trans (min_le_right _ _)
  have hout := hexclude E S hQ (hsmall.trans (min_le_left _ _))
  have hleft := N.balanced_edist_lower_of_not_mem_carrier heps
    (fun hx => hout.1 ⟨N, hN, hx⟩)
  have hright := N.balanced_edist_lower_of_not_mem_carrier heps
    (fun hx => hout.2 ⟨N, hN, hx⟩)
  have hγleft := S.path_smooth.mono (Icc_subset_Icc le_rfl hs1.le)
  have hγright := S.path_smooth.mono (Icc_subset_Icc hs0.le le_rfl)
  have hleftdist : g.edist N.center (S.path 0) ≤ g.pathELength S.path 0 s := by
    rw [← hcenter]
    change Manifold.riemannianEDist (𝓡 3) (S.path s) (S.path 0) ≤ _
    rw [Manifold.riemannianEDist_comm]
    exact Manifold.riemannianEDist_le_pathELength hγleft rfl rfl hs0.le
  have hrightdist : g.edist N.center (S.path 1) ≤ g.pathELength S.path s 1 := by
    rw [← hcenter]
    exact Manifold.riemannianEDist_le_pathELength hγright rfl rfl hs1.le
  have hL : 0 < (0.3 : ℝ) * N.scale * N.epsilon⁻¹ := by
    exact mul_pos (mul_pos (by norm_num) N.scale_pos) (inv_pos.mpr N.epsilon_pos)
  have hroom : ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹) <
      ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) := by
    apply ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (mul_pos (by norm_num) N.scale_pos) (inv_pos.mpr N.epsilon_pos)) |>.mpr
    nlinarith only [mul_pos N.scale_pos (inv_pos.mpr N.epsilon_pos)]
  obtain ⟨t₁, ht₁, hlen₁⟩ := exists_pathELength_left_anchor g hs0 hγleft hL
    (hroom.trans_le (hleft.trans hleftdist))
  obtain ⟨t₂, ht₂, hlen₂⟩ := exists_pathELength_right_anchor g hs1 hγright hL
    (hroom.trans_le (hright.trans hrightdist))
  exact ⟨t₁, ht₁, t₂, ht₂, hlen₁, hlen₂⟩

end PoincareConjecture.M28
