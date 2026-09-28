import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFrontierNecks
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

private theorem exists_first_frontier_before_endpoint
    {X : Type*} [TopologicalSpace X] {V : Set X} (hV : IsOpen V)
    {γ : ℝ → X} {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ V)
    (hb : γ b ∉ closure V) :
    ∃ c ∈ Ioo a b, γ c ∈ frontier V ∧ MapsTo γ (Ico a c) V := by
  let K : Set ℝ := Icc a b ∩ γ ⁻¹' Vᶜ
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl) inter_subset_left
  have hbK : b ∈ K :=
    ⟨right_mem_Icc.mpr hab.le, fun h => hb (subset_closure h)⟩
  obtain ⟨c, hc, hleast⟩ := hK.exists_isLeast ⟨b, hbK⟩
  have hac : a < c := by
    apply lt_of_le_of_ne hc.1.1
    rintro rfl
    exact hc.2 ha
  have hprefix : MapsTo γ (Ico a c) V := by
    intro s hs
    by_contra hout
    have hcs : c ≤ s := hleast ⟨⟨hs.1, hs.2.le.trans hc.1.2⟩, hout⟩
    exact (not_lt_of_ge hcs) hs.2
  have hclosed : MapsTo γ (Icc a c) (closure V) := by
    have hcont : ContinuousOn γ (closure (Ico a c)) := by
      rw [closure_Ico hac.ne]
      exact hγ.mono (Icc_subset_Icc le_rfl hc.1.2)
    simpa only [closure_Ico hac.ne] using hprefix.closure_of_continuousOn hcont
  have hfront : γ c ∈ frontier V := by
    rw [frontier, hV.interior_eq]
    exact ⟨hclosed (right_mem_Icc.mpr hac.le), hc.2⟩
  have hcb : c < b := by
    by_contra h
    have heq : c = b := le_antisymm hc.1.2 (le_of_not_gt h)
    apply hb
    simpa only [heq] using hclosed (right_mem_Icc.mpr hac.le)
  exact ⟨c, ⟨hac, hcb⟩, hfront, hprefix⟩

theorem exists_source_frontier_buffers_accuracy (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ N ∈ S.cover.necks, ∀ t ∈ Icc S.lower S.upper, S.path t = N.center →
          ∃ u v : ℝ, 0 < u ∧ u < t ∧ t < v ∧ v < 1 ∧
            S.path u ∈ frontier N.carrier ∧ S.path v ∈ frontier N.carrier ∧
            MapsTo S.path (Ioc u t) N.carrier ∧ MapsTo S.path (Ico t v) N.carrier ∧
            ∀ w : ℝ, w = u ∨ w = v →
              ∃ J : GeneralizedStrongNeck E.flow E.time epsilon,
                J.center = S.path w ∧
                let W := strongNeck_top J S.epsilon_lt_half
                W.carrier ⊆ S.source_region.cover.X ∧
                  S.path 0 ∉ W.carrier ∧ S.path 1 ∉ W.carrier ∧
                  ∀ p ∈ W.carrier,
                    9 * (max C 2) ^ 2 * E.flow.scalar ⟨E.time, E.basepoint⟩ ≤
                      E.flow.scalar ⟨E.time, p⟩ ∧
                    E.flow.scalar ⟨E.time, p⟩ ≤
                      (25 / 16 : ℝ) * E.flow.scalar ⟨E.time, S.path S.upper⟩ := by
  obtain ⟨epsilon₀, hpos, hsmall, hnecks⟩ := exists_source_closure_necks_accuracy P
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A D₀ D E S hQ hε N hN t ht hcenter
  obtain ⟨hzero, hone, hfresh⟩ := hnecks E S hQ hε N hN
  have ht0 : 0 < t := S.lower_pos.trans_le ht.1
  have ht1 : t < 1 := ht.2.trans_lt S.upper_lt_one
  have htN : S.path t ∈ N.carrier := by
    rw [hcenter]
    exact N.central_sphere_subset N.center_on_central_sphere
  obtain ⟨v, hv, hvfront, hright⟩ := exists_first_frontier_before_endpoint N.carrier_open
    ht1 (S.path_smooth.continuousOn.mono (Icc_subset_Icc ht0.le le_rfl)) htN hone
  let η : ℝ → (E.flow.slice E.time).carrier := fun s => S.path (t - s)
  have hη : ContinuousOn η (Icc (0 : ℝ) t) := by
    apply S.path_smooth.continuousOn.comp
      (continuous_const.sub continuous_id).continuousOn
    intro s hs
    change 0 ≤ t - s ∧ t - s ≤ 1
    exact ⟨by linarith only [hs.2], by linarith only [hs.1, ht1]⟩
  have hη0 : η 0 ∈ N.carrier := by simpa only [η, sub_zero] using htN
  have hηt : η t ∉ closure N.carrier := by simpa only [η, sub_self] using hzero
  obtain ⟨r, hr, hrfront, hleft⟩ :=
    exists_first_frontier_before_endpoint N.carrier_open ht0 hη hη0 hηt
  let u := t - r
  have hu0 : 0 < u := sub_pos.mpr hr.2
  have hut : u < t := by dsimp only [u]; linarith only [hr.1]
  have hufront : S.path u ∈ frontier N.carrier := hrfront
  have hleft' : MapsTo S.path (Ioc u t) N.carrier := by
    intro s hs
    have hsr : t - s < r := by
      have h := hs.1
      change t - r < s at h
      linarith only [h]
    have h := hleft ⟨sub_nonneg.mpr hs.2, hsr⟩
    simpa only [η, sub_sub_cancel] using h
  refine ⟨u, v, hu0, hut, hv.1, hv.2, hufront, hvfront, hleft', hright, ?_⟩
  intro w hw
  rcases hw with hwu | hwv
  · rw [hwu]
    exact hfresh u ⟨hu0.le, (hut.trans ht1).le⟩ (frontier_subset_closure hufront)
  · rw [hwv]
    exact hfresh v ⟨(ht0.trans hv.1).le, hv.2.le⟩ (frontier_subset_closure hvfront)

end PoincareConjecture.M28
