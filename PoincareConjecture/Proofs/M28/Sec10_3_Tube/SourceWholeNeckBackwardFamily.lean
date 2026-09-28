import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceWholeNeckBackwardData









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.WholeNeckBackwardData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {W : CriticalBallSourcePacket H}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
    (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))}
  {sigma : ℕ → ℕ}
  {V : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    EpsilonNeck G.limitMetric}
  (D : WholeNeckBackwardData H W G sigma V)



def sourceIndex (k : ℕ) : ℕ :=
  W.high_index (G.subsequence (sigma (k + D.offset)))



def normalization (k : ℕ) : ℝ :=
  (E (D.sourceIndex k + H.shift)).flow.scalar
    ⟨(E (D.sourceIndex k + H.shift)).time, (E (D.sourceIndex k + H.shift)).basepoint⟩



theorem normalization_pos (k : ℕ) : 0 < D.normalization k :=
  H.base_scalar_pos (D.sourceIndex k)



theorem half_window (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    V.scale ^ 2 / 2 ≤ 5 * (D.normalization k * (D.neck k).scale ^ 2) / 8 := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  have h := D.scale_lower k
  change (4 / 5 : ℝ) * V.scale ^ 2 ≤
    D.normalization k * (D.neck k).scale ^ 2 at h
  linarith only [h]



def sourceFlow (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    RicciFlow 3 (strongNeckOpen (D.neck k)) (Icc (-(V.scale ^ 2 / 2)) 0) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  exact GeneralizedStrongNeck.buffered_global_flow (D.neck k) (D.raw k)
    (D.normalization k) (D.normalization_pos k) (V.scale ^ 2 / 2)
    (half_pos (sq_pos_of_pos V.scale_pos)) (D.half_window k)



theorem sourceFlow_metric_at_zero (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (x : strongNeckOpen (D.neck k)) (v w : TangentSpace (𝓡 3) x),
      ((D.sourceFlow k).metric 0).inner x v w =
        D.normalization k *
          ((E (D.sourceIndex k + H.shift)).flow.metric
            (E (D.sourceIndex k + H.shift)).time).inner x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen (D.neck k) →
              ((E (D.sourceIndex k + H.shift)).flow.slice
                (E (D.sourceIndex k + H.shift)).time).carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen (D.neck k) →
              ((E (D.sourceIndex k + H.shift)).flow.slice
                (E (D.sourceIndex k + H.shift)).time).carrier) x w) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  exact GeneralizedStrongNeck.buffered_global_flow_metric_at_zero
    (D.neck k) (D.raw k) (D.normalization k) (D.normalization_pos k)
    (V.scale ^ 2 / 2) (half_pos (sq_pos_of_pos V.scale_pos)) (D.half_window k)



theorem sourceFlow_metric_eq_restriction (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    (D.sourceFlow k).metric 0 =
      intrinsicOpenMetric (H.normalizedSliceMetric (D.sourceIndex k))
        (strongNeckOpen (D.neck k)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  exact GeneralizedStrongNeck.buffered_global_flow_metric_eq_restriction
    (D.neck k) (D.raw k) (D.normalization k) (D.normalization_pos k)
    (V.scale ^ 2 / 2) (half_pos (sq_pos_of_pos V.scale_pos)) (D.half_window k)



theorem sourceFlow_physical_time_mem (k : ℕ) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ s ∈ Icc (-(V.scale ^ 2 / 2)) 0,
      (E (D.sourceIndex k + H.shift)).time + s / D.normalization k ∈
        (E (D.sourceIndex k + H.shift)).flow.interval := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro s hs
  exact GeneralizedStrongNeck.buffered_global_physical_time_mem
    (D.neck k) (D.normalization k) (D.normalization_pos k) (D.half_window k) hs

end PoincareConjecture.M28.CounterexampleNeckFamily.WholeNeckBackwardData
