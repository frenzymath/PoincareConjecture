import PoincareConjecture.Proofs.M15.Lemma8_7_ExponentialConfinement
import PoincareConjecture.Proofs.M15.Lemma8_8_SliceVolume
import PoincareConjecture.Proofs.M15.Prop8_2_CurvatureContractions

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M15

section Scalar

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T r : ℝ} {x : (G.slices T).Point} {K : SpacetimeInterval}
  {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  [T2Space C] [SecondCountableTopology C]

theorem actualBallCylinder_abs_scalar_le
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : M15ActualBallCylinder G T x r K C)
    (t : (G.timeIntervals.interval K).Point) (c : C) :
    |horizontalScalarCurvature G.leafwise (B.embedding.toSpacetime (t, c))| ≤
      (n : ℝ) ^ 2 * (r⁻¹) ^ 2 := by
  obtain ⟨F, _, hRm, hR⟩ := actualBallCylinder_exists_flow hM12 B
  rw [← hR t c]
  apply (abs_scalarCurvature_le_curvatureTensorNorm (F.connection t.val) c).trans
  rw [hRm t c]
  exact mul_le_mul_of_nonneg_left (B.curvature_bound t c) (sq_nonneg (n : ℝ))

end Scalar

theorem exists_actualBallCylinder_small_part_geometry
    (hM04 : RicciFlowCurvatureTheory.{u}) (n : ℕ)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 2 ∧
      ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
        (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport n X time I)
        (T : ℝ) (x : (G.slices T).Point) (r : ℝ) (K : SpacetimeInterval)
        (C : Type u) [TopologicalSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
        [T2Space C] [SecondCountableTopology C]
        (_B : M15ActualBallCylinder G T x r K C),
        IsCompact (closure ((G.slices T).metricOnPoints.ball x r)) →
        ∀ (E : M14ExponentialFamily G T x.val) (epsilon : ℝ),
          0 < epsilon → epsilon ≤ epsilon0 →
          ∀ (H : M14StableSet G T (epsilon * r ^ 2) x.val E)
            (W : Set (G.Horizontal x.val)),
            W ⊆ H.carrier →
            (∀ Z, Z ∈ W →
              Real.sqrt (G.spacetime.horizontalMetric.inner x.val Z Z) ≤
                1 / (8 * Real.sqrt epsilon)) →
            (∀ Z, Z ∈ W → ∀ s ∈ Ioo 0 (epsilon * r ^ 2),
              -(n : ℝ) ^ 2 * (r⁻¹) ^ 2 ≤
                horizontalScalarCurvature G.leafwise (E.gamma Z (Real.sqrt s))) ∧
            calibratedMetricVolume (G.slices (T - epsilon * r ^ 2)).metricOnPoints
              (H.endpoint_slice_map '' W) < ⊤ ∧
            calibratedMetricVolume (G.slices (T - epsilon * r ^ 2)).metricOnPoints
              (H.endpoint_slice_map '' W) ≤
              ENNReal.ofReal (Real.exp ((n : ℝ) * epsilon)) ^ n *
                calibratedMetricVolume (G.slices T).metricOnPoints
                  ((G.slices T).metricOnPoints.ball x r) := by
  obtain ⟨epsilon0, hepsilon0, hepsilon0half, hconf⟩ :=
    exists_actualBallCylinder_exponential_confinement hM04 n hM12 hM13
  refine ⟨epsilon0, hepsilon0, hepsilon0half, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact E epsilon hepsilon hepsilon_le
    H W hWH hsmall
  have hr := B.radius_pos
  have ha : 0 < Real.sqrt (epsilon * r ^ 2) := Real.sqrt_pos.mpr H.tau_pos
  have hSr : Real.sqrt (epsilon * r ^ 2) ≤ Real.sqrt epsilon * r := by
    rw [Real.sqrt_mul hepsilon.le, Real.sqrt_sq hr.le]
  have hlift (Z : G.Horizontal x.val) (hZ : Z ∈ W) :=
    hconf X time I G T x r K C B hcompact E epsilon hepsilon hepsilon_le
      (Real.sqrt (epsilon * r ^ 2)) ha Z (H.survivor Z (hWH hZ))
      (Real.sqrt (epsilon * r ^ 2)) ha.le le_rfl hSr (hsmall Z hZ)
  have ht : T - epsilon * r ^ 2 ∈ K.domain := by
    rw [B.interval_domain]
    have he : epsilon ≤ 1 / 2 := hepsilon_le.trans hepsilon0half
    constructor <;> nlinarith [sq_nonneg r,
      mul_le_mul_of_nonneg_right he (sq_nonneg r), H.tau_pos]
  let t : (G.timeIntervals.interval K).Point := ⟨T - epsilon * r ^ 2, ht⟩
  let V : Set C := {c | (G.slices T).metricOnPoints.edist x (B.source_map c) ≤
    ENNReal.ofReal (5 * r / 12)}
  have himage : H.endpoint_slice_map '' W ⊆
      movingGaugeSliceMap B.embedding.toMovingSpacetimeGauge G.slices t '' V := by
    rintro q ⟨Z, hZ, rfl⟩
    obtain ⟨L, _, hL⟩ := hlift Z hZ
    have haI : Real.sqrt (epsilon * r ^ 2) ∈ Icc 0 (Real.sqrt (epsilon * r ^ 2)) :=
      ⟨ha.le, le_rfl⟩
    have hend := (hL _ haI).1
    have htime := congrArg G.spacetime.timeFunction hend
    rw [B.embedding.time_eq, E.clock Z _ (H.survivor Z (hWH hZ)),
      Real.sq_sqrt H.tau_pos.le] at htime
    have hLt : (L (Real.sqrt (epsilon * r ^ 2))).1 = t := Subtype.ext htime
    refine ⟨(L (Real.sqrt (epsilon * r ^ 2))).2, (hL _ haI).2.1, ?_⟩
    apply Subtype.ext
    change B.embedding.toSpacetime (t, (L (Real.sqrt (epsilon * r ^ 2))).2) = _
    calc
      _ = B.embedding.toSpacetime (L (Real.sqrt (epsilon * r ^ 2))) :=
        (congrArg (fun z => B.embedding.toSpacetime
          (z, (L (Real.sqrt (epsilon * r ^ 2))).2)) hLt).symm
      _ = E.gamma Z (Real.sqrt (epsilon * r ^ 2)) := hend
      _ = (H.endpoint_slice_map Z).val :=
        ((H.endpoint_slice_map_val Z (hWH hZ)).trans (H.endpoint_map_eq Z (hWH hZ))).symm
  obtain ⟨hbuffer, hvolume⟩ := actualBallCylinder_compact_slice_buffer hM12 B hcompact t
  refine ⟨?_, (measure_mono himage).trans_lt
    (calibratedMetricVolume_lt_top_of_isCompact _ hbuffer), ?_⟩
  · intro Z hZ s hs
    obtain ⟨L, _, hL⟩ := hlift Z hZ
    have hsqrt : Real.sqrt s ∈ Icc 0 (Real.sqrt (epsilon * r ^ 2)) :=
      ⟨Real.sqrt_nonneg s, Real.sqrt_le_sqrt hs.2.le⟩
    have hscalar := actualBallCylinder_abs_scalar_le hM12 B
      (L (Real.sqrt s)).1 (L (Real.sqrt s)).2
    rw [(hL _ hsqrt).1] at hscalar
    have h := (abs_le.mp hscalar).1
    linarith
  · have hexponent : (n : ℝ) * (r⁻¹) ^ 2 * (T - t.val) = (n : ℝ) * epsilon := by
      dsimp only [t]
      field_simp
      ring
    rw [hexponent] at hvolume
    exact (measure_mono himage).trans hvolume

end PoincareConjecture.Proofs.M15
