import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallWholeNeighborhoodProducer
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckBufferedGlobalBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 1600000 in



structure WholeNeckBackwardData
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k)))
    (sigma : ℕ → ℕ)
    (V : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      EpsilonNeck G.limitMetric) where

  offset : ℕ

  epsilon_small : epsilon < 1 / 2

  epsilon_limit : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    V.epsilon = 3 * epsilon / 2

  neck : ∀ k, GeneralizedStrongNeck
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time epsilon

  raw : ∀ k, RescaledRawCylinderData
    (C := (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow.slice
      (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time)
    (U := strongNeckOpen (neck k)) (J := strongNeckBackwardInterval)
    (strongNeckCylinder (neck k)) (GeneralizedStrongNeck.physical_interval_subset (neck k))

  center_eq : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, (neck k).center =
    (G.embedding (sigma (k + offset)) V.center).val.val

  exhaustion : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, V.carrier ⊆ G.exhaustion (sigma (k + offset))

  scale_lower : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k, (4 / 5 : ℝ) * V.scale ^ 2 ≤
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow.scalar
      ⟨(E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time,
        (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).basepoint⟩ *
          (neck k).scale ^ 2

  scale_upper : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k,
    (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).flow.scalar
      ⟨(E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).time,
        (E (W.high_index (G.subsequence (sigma (k + offset))) + H.shift)).basepoint⟩ *
          (neck k).scale ^ 2 ≤ (6 / 5 : ℝ) * V.scale ^ 2

  capture : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ k y, y ∈ V.carrier →
    |(V.coordinate_inverse y).2| ≤ 3 * epsilon⁻¹ / 5 →
      (G.embedding (sigma (k + offset)) y).val.val ∈ (neck k).carrier ∧
      |((neck k).coordinate_inverse (G.embedding (sigma (k + offset)) y).val.val).2| <
        3 * epsilon⁻¹ / 4

set_option maxHeartbeats 2400000 in




theorem exists_whole_neck_backward_data
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (sigma : ℕ → ℕ), StrictMono sigma →
      ∀ (V : EpsilonNeck G.limitMetric), V.epsilon = 3 * epsilon / 2 →
      (∃ j : ℕ, V.carrier ⊆ G.exhaustion j) →
      ∀ (J : ∀ k, GeneralizedStrongNeck
        (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow
        (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time epsilon),
        (∀ k, (J k).center = (G.embedding (sigma k) V.center).val.val) →
        Tendsto (fun k =>
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
            ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
              (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩ *
                (J k).scale ^ 2) atTop (𝓝 (V.scale ^ 2)) →
        (∀ᶠ k in atTop, ∀ y ∈ V.carrier,
          |(V.coordinate_inverse y).2| ≤ 3 * epsilon⁻¹ / 5 →
            (G.embedding (sigma k) y).val.val ∈ (J k).carrier ∧
            |((J k).coordinate_inverse (G.embedding (sigma k) y).val.val).2| <
              3 * epsilon⁻¹ / 4) →
        Nonempty (WholeNeckBackwardData H W G sigma V) := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro sigma hsigma V hV hj J hcenter hconv hcapture
  obtain ⟨j, hstage⟩ := hj
  have hpos : 0 < V.scale ^ 2 := sq_pos_of_pos V.scale_pos
  have hlower := hconv.eventually
    (eventually_ge_nhds (show (4 / 5 : ℝ) * V.scale ^ 2 < V.scale ^ 2 by linarith))
  have hupper := hconv.eventually
    (eventually_le_nhds (show V.scale ^ 2 < (6 / 5 : ℝ) * V.scale ^ 2 by linarith))
  have hindices := hsigma.tendsto_atTop.eventually (eventually_ge_atTop j)
  obtain ⟨offset, hoffset⟩ := eventually_atTop.mp
    (hcapture.and (hlower.and (hupper.and hindices)))
  have htail (k : ℕ) := hoffset (k + offset) (by omega)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  exact ⟨{
    offset := offset
    epsilon_small := by linarith [V.epsilon_lt_half]
    epsilon_limit := hV
    neck := fun k => J (k + offset)
    raw := fun k => Classical.choice
      (GeneralizedStrongNeck.exists_rescaled_raw_cylinder_flow (J (k + offset)))
    center_eq := fun k => hcenter (k + offset)
    exhaustion := fun k => hstage.trans (hmono (htail k).2.2.2)
    scale_lower := fun k => (htail k).2.1
    scale_upper := fun k => (htail k).2.2.1
    capture := fun k => (htail k).1 }⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
