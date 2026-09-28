import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFinalChartReadouts









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

set_option backward.isDefEq.respectTransparency true in



structure RetainedFinalSourceData
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k)))
    (D0 : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      LeviCivitaData G.limitMetric)
    (q : ℕ → G.limitCarrier.carrier) (sigma : ℕ → ℕ) where

  column : ℕ → ℕ

  column_strictMono : StrictMono column

  stage : ℕ → ℕ

  neck : ∀ i : ℕ, GeneralizedStrongNeck
    (E (W.high_index (G.subsequence (sigma (column i))) + H.shift)).flow
    (E (W.high_index (G.subsequence (sigma (column i))) + H.shift)).time epsilon

  center_eq : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, (neck i).center = (G.embedding (sigma (column i)) (q i)).val.val

  scalar_pos : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, 0 < D0.scalarCurvature (q i)

  readouts : FinalSourceDiagonalReadouts H W G D0 q sigma column stage neck

namespace RetainedFinalSourceData

variable {H : CounterexampleNeckFamily E} {W : CriticalBallSourcePacket H}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
    (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))}
  {D0 : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    LeviCivitaData G.limitMetric}
  {q : ℕ → G.limitCarrier.carrier} {sigma : ℕ → ℕ}



theorem stage_guard (D : RetainedFinalSourceData H W G D0 q sigma) (i : ℕ) :
    q i ∈ G.exhaustion (D.stage i) ∧ D.stage i + 1 ≤ sigma (D.column i) := by
  exact ⟨(D.readouts i).1, (D.readouts i).2.1⟩



theorem scale_error (D : RetainedFinalSourceData H W G D0 q sigma) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, let e := E (W.high_index (G.subsequence (sigma (D.column i))) + H.shift)
      |D0.scalarCurvature (q i) *
        (e.flow.scalar ⟨e.time, e.basepoint⟩ * (D.neck i).scale ^ 2) - 1| ≤
          (1 : ℝ) / ((i : ℝ) + 2) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i e
  exact (D.readouts i).2.2.1



theorem base_lower (D : RetainedFinalSourceData H W G D0 q sigma) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, let e := E (W.high_index (G.subsequence (sigma (D.column i))) + H.shift)
      2 * ((i : ℝ) + 1) / D0.scalarCurvature (q i) ≤
        e.flow.scalar ⟨e.time, e.basepoint⟩ := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i e
  exact (D.readouts i).2.2.2.1



theorem normalization_lower (D : RetainedFinalSourceData H W G D0 q sigma)
    (i : ℕ) : ((i : ℝ) + 1) ≤ ((D.neck i).scale⁻¹) ^ 2 := by
  exact (D.readouts i).2.2.2.2.1

set_option maxHeartbeats 3200000 in



theorem metric_bounds (D : RetainedFinalSourceData H W G D0 q sigma) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, let delta := (1 : ℝ) / ((i : ℝ) + 2)
      let nu := W.high_index (G.subsequence (sigma (D.column i)))
      ∀ x ∈ closure (G.exhaustion (D.stage i)), ∀ v : TangentSpace (𝓡 3) x,
        (1 + delta)⁻¹ * G.limitMetric.inner x v v ≤
          (H.tubeCriticalMetric W.tube W.radius nu).inner
            (G.embedding (sigma (D.column i)) x)
            (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma (D.column i))) x v)
            (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma (D.column i))) x v) ∧
        (H.tubeCriticalMetric W.tube W.radius nu).inner
          (G.embedding (sigma (D.column i)) x)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma (D.column i))) x v)
          (mfderiv (𝓡 3) (𝓡 3) (G.embedding (sigma (D.column i))) x v) ≤
            (1 + delta) * G.limitMetric.inner x v v := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i delta nu
  exact (D.readouts i).2.2.2.2.2.1



theorem scalar_error (D : RetainedFinalSourceData H W G D0 q sigma) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, let e := E (W.high_index (G.subsequence (sigma (D.column i))) + H.shift)
      ∀ x ∈ closure (G.exhaustion (D.stage i)),
        |e.flow.scalar ⟨e.time, (G.embedding (sigma (D.column i)) x).val.val⟩ /
          e.flow.scalar ⟨e.time, e.basepoint⟩ - D0.scalarCurvature x| ≤ 1 := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i e
  exact (D.readouts i).2.2.2.2.2.2.1

set_option maxHeartbeats 3200000 in



theorem inverse_center (D : RetainedFinalSourceData H W G D0 q sigma) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
      W.high_index G (sigma (D.column i))).symm (D.neck i).center = q i := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i
  exact (D.readouts i).2.2.2.2.2.2.2.1

set_option maxHeartbeats 3200000 in



theorem core_capture (D : RetainedFinalSourceData H W G D0 q sigma) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ,
      let e := H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
        W.high_index G (sigma (D.column i))
      ∀ x ∈ (D.neck i).carrier,
        |((D.neck i).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
          x ∈ e.target ∧ e.symm x ∈ G.exhaustion (D.stage i) ∧ e (e.symm x) = x := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro i e
  exact (D.readouts i).2.2.2.2.2.2.2.2

end RetainedFinalSourceData

set_option maxHeartbeats 3200000 in




theorem exists_retained_final_source_data_accuracy (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D0 : LeviCivitaData G.limitMetric) (q : ℕ → G.limitCarrier.carrier)
            (L : EpsilonNeck G.limitMetric), L.center = G.base →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              (∀ i, ∀ᶠ k in atTop, (G.embedding (sigma k) (q i)).val.val ∉
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) →
              Nonempty (RetainedFinalSourceData H W G D0 q sigma) := by
  classical
  obtain ⟨epsilon0, hpos, hsmall, hrow⟩ :=
    exists_retained_strong_neck_core_capture_accuracy P
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q L hL sigma hsigma f hf hbound hgraphs hside
  let nu := fun k => W.high_index (G.subsequence (sigma k))
  let Q := fun k => (E (nu k + H.shift)).flow.scalar
    ⟨(E (nu k + H.shift)).time, (E (nu k + H.shift)).basepoint⟩
  let R := fun i => D0.scalarCurvature (q i)
  have hrows (i : ℕ) :
      ∃ J : ∀ k, GeneralizedStrongNeck
        (E (nu k + H.shift)).flow (E (nu k + H.shift)).time epsilon,
        (∀ k, (J k).center = (G.embedding (sigma k) (q i)).val.val) ∧
        0 < (R i)⁻¹ ∧
        Tendsto (fun k => Q k * (J k).scale ^ 2) atTop (𝓝 (R i)⁻¹) ∧
        ∃ j : ℕ, ∀ᶠ k in atTop, j ≤ sigma k ∧ ∀ x ∈ (J k).carrier,
          |((J k).coordinate_inverse x).2| ≤ 2 * epsilon⁻¹ / 3 →
            x ∈ (fun y => (G.embedding (sigma k) y).val.val) '' G.exhaustion j :=
    hrow H W hepsilon G D0 (q i) L hL sigma hsigma f hf hbound hgraphs (hside i)
  choose J hcenter hpositive hscale hcapture using hrows
  have hRpos (i : ℕ) : 0 < R i := inv_pos.mp (hpositive i)
  obtain ⟨j, kappa, hkappa, hdata⟩ := H.exists_source_final_chart_diagonal
    W G D0 q sigma hsigma J hcenter hRpos hscale hcapture
  refine ⟨{
    column := kappa
    column_strictMono := hkappa
    stage := j
    neck := fun i => J i (kappa i)
    center_eq := fun i => hcenter i (kappa i)
    scalar_pos := hRpos
    readouts := hdata }⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
