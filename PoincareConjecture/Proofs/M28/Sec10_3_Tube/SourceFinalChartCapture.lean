import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFinalChartDiagonal
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckInverseCenterScalar
import PoincareConjecture.Proofs.M28.Mathlib.ConnectedFrontierBarrier
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import Mathlib.Analysis.Convex.PathConnected











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3200000 in





theorem exists_source_final_chart_capture_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
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
            (sigma kappa j : ℕ → ℕ),
          let nu := fun i => W.high_index (G.subsequence (sigma (kappa i)))
          let Q := fun i => (E (nu i + H.shift)).flow.scalar
            ⟨(E (nu i + H.shift)).time, (E (nu i + H.shift)).basepoint⟩
          let Ri := fun i => D0.scalarCurvature (q i)
          let e := fun i => H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
            W.high_index G (sigma (kappa i))
          ∀ (S : ∀ i, GeneralizedStrongNeck (E (nu i + H.shift)).flow
            (E (nu i + H.shift)).time epsilon)
            (Hraw : ∀ i, RescaledRawCylinderData
              (C := (E (nu i + H.shift)).flow.slice (E (nu i + H.shift)).time)
              (U := strongNeckOpen (S i)) (J := strongNeckBackwardInterval)
              (strongNeckCylinder (S i))
              (GeneralizedStrongNeck.physical_interval_subset (S i)))
            {R0 : ℝ}, 0 < R0 → R0 < 1 / 8 →
          ∀ (Phi : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen (S i)) ∞),
            (∀ i, (Phi i).source = Metric.ball 0 R0 ∧
              (Phi i).target =
                ((GeneralizedStrongNeck.rescaled_half_flow (S i) (Hraw i)).metric 0).ball
                  (strongNeckSourceCenter (S i)) R0 ∧
              Phi i 0 = strongNeckSourceCenter (S i)) →
            (∀ i, 0 < Ri i) →
            (∀ i, |Ri i * (Q i * (S i).scale ^ 2) - 1| ≤
              (1 : ℝ) / ((i : ℝ) + 2)) →
            (∀ i, ∀ x ∈ closure (G.exhaustion (j i)),
              |(E (nu i + H.shift)).flow.scalar
                  ⟨(E (nu i + H.shift)).time,
                    (G.embedding (sigma (kappa i)) x).val.val⟩ / Q i -
                D0.scalarCurvature x| ≤ 1) →
            (∀ i, (e i).symm (S i).center = q i) →
            (∀ i, ∀ y ∈ (S i).carrier,
              |((S i).coordinate_inverse y).2| ≤ 2 * epsilon⁻¹ / 3 →
                y ∈ (e i).target ∧ (e i).symm y ∈ G.exhaustion (j i) ∧
                  e i ((e i).symm y) = y) →
          ∀ (U : TopologicalSpace.Opens G.limitCarrier.carrier)
            {Y : Set G.limitCarrier.carrier} (B : OpenCylinderModel Y),
            frontier (U : Set G.limitCarrier.carrier) = B.middleSphere →
            (∀ i, q i ∈ (U : Set G.limitCarrier.carrier)) →
            Tendsto Ri atTop atTop →
          let Psi := fun i => inverseStrongNeckCenterChart (S i) (Phi i) (e i)
          (∀ i, (Psi i).source = Metric.ball 0 R0 ∧ Psi i 0 = q i ∧
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Psi i) (Metric.ball 0 R0) ∧
            ContinuousOn (Psi i) (Metric.ball 0 R0) ∧
            IsOpen (Psi i '' Metric.ball 0 R0) ∧
            Psi i '' Metric.ball 0 R0 ⊆ G.exhaustion (j i) ∧
            ∀ z ∈ Metric.ball 0 R0,
              Ri i / 4 - 1 ≤ D0.scalarCurvature (Psi i z)) ∧
          ∀ᶠ i in atTop, Psi i '' Metric.ball 0 R0 ⊆ (U : Set G.limitCarrier.carrier) := by
  obtain ⟨epsilon0, hpos, hsmall, hscalarLower⟩ :=
    exists_inverseStrongNeckCenterChart_scalar_lower_accuracy.{u, 0}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0 q sigma kappa j
  dsimp only
  intro S Hraw R0 hR0 hRsmall Phi hPhi hpositive hscale hscalar hcenter hcore
    U Y B hfront hqU hdiverge
  let nu := fun i => W.high_index (G.subsequence (sigma (kappa i)))
  let Q := fun i => (E (nu i + H.shift)).flow.scalar
    ⟨(E (nu i + H.shift)).time, (E (nu i + H.shift)).basepoint⟩
  let Ri := fun i => D0.scalarCurvature (q i)
  let e := fun i => H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
    W.high_index G (sigma (kappa i))
  let Psi := fun i => inverseStrongNeckCenterChart (S i) (Phi i) (e i)
  have hcore' (i : ℕ) : ∀ y ∈ (S i).carrier,
      |((S i).coordinate_inverse y).2| ≤ 2 * epsilon⁻¹ / 3 →
        y ∈ (e i).target ∧ (e i).symm y ∈ G.exhaustion (j i) := by
    intro y hy hh
    exact ⟨(hcore i y hy hh).1, (hcore i y hy hh).2.1⟩
  have hread (i : ℕ) := inverseStrongNeckCenterChart_domain (S i) (Hraw i)
    (hepsilon.trans hsmall) hRsmall (Phi i) (hPhi i).1 (hPhi i).2.1
    (e i) (G.exhaustion (j i)) (hcore' i)
  have hzero (i : ℕ) : Psi i 0 = q i :=
    inverseStrongNeckCenterChart_zero (S i) (Phi i) (hPhi i).2.2 (e i) (hcenter i)
  have hscaleUpper (i : ℕ) : Ri i * (Q i * (S i).scale ^ 2) ≤ 2 := by
    have hdelta : (1 : ℝ) / ((i : ℝ) + 2) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 2)).2
      nlinarith only [Nat.cast_nonneg (α := ℝ) i]
    have hh := (abs_le.mp (hscale i)).2
    linarith only [hh, hdelta]
  have hlower (i : ℕ) : ∀ z ∈ Metric.ball 0 R0,
      Ri i / 4 - 1 ≤ D0.scalarCurvature (Psi i z) := by
    apply hscalarLower (S i) (Hraw i) hepsilon G.limitCarrier.carrier
      G.limitMetric D0 hRsmall (Phi i) (hPhi i).1 (hPhi i).2.1
      (e i) (G.exhaustion (j i)) (hcore' i) (Q i) (Ri i)
      (H.base_scalar_pos (nu i)) (hpositive i) (hscaleUpper i)
    intro x hx
    exact hscalar i x (subset_closure hx)
  have hfrontCompact : IsCompact (frontier (U : Set G.limitCarrier.carrier)) := by
    rw [hfront]
    exact B.isCompact_middleSphere
  have hballConnected : IsConnected (Metric.ball (0 : E3) R0) :=
    (convex_ball (0 : E3) R0).isConnected ⟨0, Metric.mem_ball_self hR0⟩
  have hboundDiverges : Tendsto (fun i => Ri i / 4 - 1) atTop atTop := by
    refine tendsto_atTop.2 fun bound => ?_
    filter_upwards [hdiverge.eventually_ge_atTop (4 * (bound + 1))] with i hi
    linarith only [hi]
  have hinside : ∀ᶠ i in atTop,
      Psi i '' Metric.ball 0 R0 ⊆ (U : Set G.limitCarrier.carrier) :=
    eventually_image_subset_of_compact_frontier_barrier U.isOpen hfrontCompact
      D0.scalarCurvature D0.continuous_scalarCurvature.continuousOn hballConnected
      (fun i => Psi i) (fun i => (hread i).2.2.2.1) (Metric.mem_ball_self hR0)
      (fun i => by rw [hzero i]; exact hqU i)
      (fun i => Ri i / 4 - 1) hboundDiverges (Eventually.of_forall hlower)
  refine ⟨?_, hinside⟩
  intro i
  exact ⟨(hread i).1, hzero i, (hread i).2.2.1, (hread i).2.2.2.1,
    (hread i).2.2.2.2.1, (hread i).2.2.2.2.2, hlower i⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
