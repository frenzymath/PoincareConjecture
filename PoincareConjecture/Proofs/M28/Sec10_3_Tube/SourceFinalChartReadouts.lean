import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFinalChartDiagonal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 3200000 in

def FinalSourceDiagonalReadouts
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k)))
    (D0 : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      LeviCivitaData G.limitMetric)
    (q : ℕ → G.limitCarrier.carrier) (sigma column stage : ℕ → ℕ)
    (neck : ∀ i : ℕ, GeneralizedStrongNeck
      (E (W.high_index (G.subsequence (sigma (column i))) + H.shift)).flow
      (E (W.high_index (G.subsequence (sigma (column i))) + H.shift)).time epsilon) :
    Prop :=
  letI := G.limitCarrier.topologicalSpace
  letI := G.limitCarrier.chartedSpace
  letI := G.limitCarrier.isManifold
  let nu := fun k => W.high_index (G.subsequence (sigma k))
  let Q := fun k => (E (nu k + H.shift)).flow.scalar
    ⟨(E (nu k + H.shift)).time, (E (nu k + H.shift)).basepoint⟩
  let R := fun i => D0.scalarCurvature (q i)
  let delta := fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 2)
  ∀ i : ℕ,
    let k := column i
    let e := H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
      W.high_index G (sigma k)
    q i ∈ G.exhaustion (stage i) ∧
    stage i + 1 ≤ sigma k ∧
    |R i * (Q k * (neck i).scale ^ 2) - 1| ≤ delta i ∧
    2 * ((i : ℝ) + 1) / R i ≤ Q k ∧
    ((i : ℝ) + 1) ≤ ((neck i).scale⁻¹) ^ 2 ∧
    (∀ x ∈ closure (G.exhaustion (stage i)),
      ∀ v : TangentSpace (𝓡 3) x,
        (1 + delta i)⁻¹ * G.limitMetric.inner x v v ≤
          (H.tubeCriticalMetric W.tube W.radius (nu k)).inner
            (G.embedding (sigma k) x)
            (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v)
            (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v) ∧
        (H.tubeCriticalMetric W.tube W.radius (nu k)).inner
          (G.embedding (sigma k) x)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma k)) x v) ≤
            (1 + delta i) * G.limitMetric.inner x v v) ∧
    (∀ x ∈ closure (G.exhaustion (stage i)),
      |(E (nu k + H.shift)).flow.scalar
          ⟨(E (nu k + H.shift)).time,
            (G.embedding (sigma k) x).val.val⟩ / Q k -
          D0.scalarCurvature x| ≤ 1) ∧
    e.symm (neck i).center = q i ∧
    (∀ x ∈ (neck i).carrier,
      |((neck i).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
        x ∈ e.target ∧ e.symm x ∈ G.exhaustion (stage i) ∧ e (e.symm x) = x)

end PoincareConjecture.M28.CounterexampleNeckFamily
