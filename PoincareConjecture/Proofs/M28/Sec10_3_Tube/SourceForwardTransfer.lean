import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckQuarterOverlap
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalForwardTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckSegment

variable {epsilon C A D₀ D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D₀ D}

theorem exists_source_frontier_oriented_forward_accuracy
    (S : CounterexampleNeckSegment E) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (_hsmall : epsilon ≤ epsilon₀), ∃ N : ℝ → EpsilonNeck (E.flow.metric E.time),
      (∀ s ∈ Icc S.lower S.upper,
        N s ∈ S.cover.necks ∧ (N s).center = S.path s) ∧
      ∃ l : List ℝ,
        (∀ s ∈ S.lower :: l, s ∈ Icc S.lower S.upper) ∧
        (S.lower :: l).IsChain (fun s t =>
          s < t ∧ S.path t ∈ frontier (N s).carrier ∧
            MapsTo S.path (Ico s t) (N s).carrier) ∧
        (∀ s t, s ∈ S.lower :: l → t ∈ S.lower :: l →
          s < t → S.path t ∈ frontier (N s).carrier →
          MapsTo S.path (Ico s t) (N s).carrier →
          ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
            (N t).center ∈ closure (neckSignedRegion (N s) sigma
              ((N s).epsilon⁻¹ / 2) (N s).epsilon⁻¹) ∧
            ∃ Q : EpsilonNeck (E.flow.metric E.time),
              (Q = N t ∨ Q = (N t).reversed) ∧
              neckSignedRegion (N s) sigma ((N s).epsilon⁻¹ / 2)
                  (N s).epsilon⁻¹ ⊆
                Q.region (-(N s).epsilon⁻¹) ((N s).epsilon⁻¹ / 2)) := by
  obtain ⟨epsilonQ, hQpos, hQsmall, hQ⟩ :=
    exists_source_frontier_quarter_accuracy S
  obtain ⟨epsilonF, hFpos, hFsmall, hF⟩ :=
    EpsilonNeck.exists_oriented_forward_transfer_accuracy.{u}
  let epsilon₀ := min epsilonQ epsilonF
  refine ⟨epsilon₀, lt_min hQpos hFpos,
    (min_le_left _ _).trans hQsmall, ?_⟩
  intro hsmall
  obtain ⟨N, hN, l, hlmem, hlchain, hedge⟩ :=
    hQ (hsmall.trans (min_le_left _ _))
  refine ⟨N, hN, l, hlmem, hlchain, ?_⟩
  intro s t hs ht hst hfront hmap
  obtain ⟨sigma, hsigma, hcenter, hcarrier⟩ :=
    hedge s t hs ht hst hfront hmap
  have hsI : s ∈ Icc S.lower S.upper := hlmem s hs
  have htI : t ∈ Icc S.lower S.upper := hlmem t ht
  have hNs : (N s).epsilon = epsilon :=
    (S.cover.neck_epsilon (N s) (hN s hsI).1).trans S.cover_epsilon
  have hNt : (N t).epsilon = epsilon :=
    (S.cover.neck_epsilon (N t) (hN t htI).1).trans S.cover_epsilon
  have heq : (N t).epsilon = (N s).epsilon := hNt.trans hNs.symm
  have hsmallF : (N s).epsilon ≤ epsilonF := by
    rw [hNs]
    exact hsmall.trans (min_le_right _ _)
  have hfrontCenter : (N t).center ∈ frontier (N s).carrier := by
    rw [(hN t htI).2]
    exact hfront
  have houtside : (N t).center ∉ (N s).carrier := by
    rw [(N s).carrier_open.frontier_eq] at hfrontCenter
    exact hfrontCenter.2
  rcases hsigma with rfl | rfl
  · have hcenter' : (N t).center ∈
        closure ((N s).region ((N s).epsilon⁻¹ / 2) (N s).epsilon⁻¹) := by
      simpa only [neckSignedRegion_one] using hcenter
    obtain ⟨Q, hQ, _, hQregion⟩ := hF (N s) (N t) hsmallF heq hcenter' houtside
    refine ⟨1, Or.inl rfl, hcenter, Q, ?_, ?_⟩
    · exact hQ
    · simpa only [neckSignedRegion_one] using hQregion
  · let R := (N s).reversed
    have hRε : R.epsilon = (N s).epsilon := EpsilonNeck.reversed_epsilon _
    have hcenter' : (N t).center ∈
        closure (R.region (R.epsilon⁻¹ / 2) R.epsilon⁻¹) := by
      simpa only [R, neckSignedRegion_neg_one, EpsilonNeck.reversed_region,
        EpsilonNeck.reversed_epsilon] using hcenter
    have houtR : (N t).center ∉ R.carrier := by
      simpa only [R, EpsilonNeck.reversed_carrier] using houtside
    obtain ⟨Q, hQ, _, hQregion⟩ := hF R (N t)
      (hRε ▸ hsmallF) heq hcenter' houtR
    refine ⟨-1, Or.inr rfl, hcenter, Q, ?_, ?_⟩
    · exact hQ
    · simpa only [R, neckSignedRegion_neg_one, EpsilonNeck.reversed_region,
        EpsilonNeck.reversed_epsilon] using hQregion

end PoincareConjecture.M28.CounterexampleNeckSegment
