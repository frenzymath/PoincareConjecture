import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Geometry.SourceFinalChartReadouts

/-!
# The actual original-source diagonal at prescribed limit points

A constructed record retains the literal source columns and all proved
guarded metric and scalar readouts. The incoming row of limit points
is unchanged. Source: Morgan--Tian pp. 263-265; derivations 136 and 161a.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 3200000 in
-- The source necks and comparisons retain the same dependent original index.
set_option backward.isDefEq.respectTransparency true in
/-- Only outputs of the actual source-row and diagonal producers are
stored. The connection, row points and source orientation are fixed
parameters. Source: MT pp. 263-265; derivations 136 and 161a. -/
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
  /-- Source columns selected without changing the prescribed row points. -/
  column : ℕ → ℕ
  /-- The source-column selection remains cofinal. -/
  column_strictMono : StrictMono column
  /-- A single guarded limit stage for each selected original neck. -/
  stage : ℕ → ℕ
  /-- The actual strong neck on the original retained counterexample. -/
  neck : ∀ i : ℕ, GeneralizedStrongNeck
    (E (W.high_index (G.subsequence (sigma (column i))) + H.shift)).flow
    (E (W.high_index (G.subsequence (sigma (column i))) + H.shift)).time epsilon
  /-- Its center is the literal source image of the same prescribed point. -/
  center_eq : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, (neck i).center = (G.embedding (sigma (column i)) (q i)).val.val
  /-- Positivity follows from the constructed row's normalized neck scale. -/
  scalar_pos : letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ i : ℕ, 0 < D0.scalarCurvature (q i)
  /-- The exact nine checked diagonal readouts share one proposition. -/
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

/-- The retained row point and one extra exhaustion stage are captured.
Source: the first two readouts of the actual diagonal, derivation 136. -/
theorem stage_guard (D : RetainedFinalSourceData H W G D0 q sigma) (i : ℕ) :
    q i ∈ G.exhaustion (D.stage i) ∧ D.stage i + 1 ≤ sigma (D.column i) := by
  exact ⟨(D.readouts i).1, (D.readouts i).2.1⟩

/-- The original neck normalization has the checked vanishing error.
Source: the third readout of the actual diagonal, derivation 136. -/
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

/-- The original base scalar dominates the prescribed row threshold.
Source: the fourth readout of the actual diagonal, derivation 136. -/
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

/-- The original source curvature normalization diverges along the row.
Source: the fifth readout of the actual diagonal, derivation 136. -/
theorem normalization_lower (D : RetainedFinalSourceData H W G D0 q sigma)
    (i : ℕ) : ((i : ℝ) + 1) ≤ ((D.neck i).scale⁻¹) ^ 2 := by
  exact (D.readouts i).2.2.2.2.1

set_option maxHeartbeats 3200000 in
-- This one accessor keeps the same dependent source metric and derivative.
/-- Both quadratic bounds hold on the original captured compact stage.
Source: the sixth readout of the actual diagonal, derivation 136. -/
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

/-- The normalized original scalar has absolute error at most one.
Source: the seventh readout of the actual diagonal, derivation 136. -/
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
-- The raw map retains both actual open inclusions and its original slice.
/-- The actual raw inverse sends the original neck center to the row point.
Source: the eighth readout of the actual diagonal, derivation 136. -/
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
-- The guarded inverse and its target use one literal original source map.
/-- The entire buffered original neck core has an inverse in the same stage.
Source: the ninth readout of the actual diagonal, derivation 136. -/
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
-- Keep fixed point rows separate from the selected source columns.
/-- Actual positive-side original strong necks construct the retained
diagonal record at every prescribed row of limit points. No normal
chart or limit flow is an input. Source: derivations 116, 136 and 161a. -/
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

end PoincareMT.M28.CounterexampleNeckFamily
