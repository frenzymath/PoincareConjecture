import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardFamily

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 2400000 in

theorem exists_source_criticalBall_backward_family_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric T A1 (phi k))
            (fun k => H.tubeCriticalBase T A1 hA1 (phi k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
            let a := (D₀.scalarCurvature q)⁻¹
            ∃ D : CriticalBallBackwardChartData H T A1 hA1 phi G q a,
              (∃ K : ℝ, 0 < K ∧ ∀ k t, t ∈ Icc (-(a / 8)) 0 →
                ∀ x : strongNeckOpen (D.neck k),
                  ((D.sourceFlow k).connection t).curvatureTensorNorm x ≤ K) ∧
              ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ k t, t ∈ Icc (-(a / 8)) 0 →
                ∀ x ∈ D.domain,
                  ((D.sourceFlow k).connection t).curvatureDerivativeNorm m
                    (D.parametrization k x) ≤ B := by
  obtain ⟨epsilonD, hDpos, hDsmall, hdata⟩ :=
    exists_source_criticalBall_backward_chart_data_accuracy P
  obtain ⟨epsilonB, hBpos, _, K, hK, hbounds⟩ :=
    exists_strongNeck_global_bounds_accuracy P.local_derivative_estimates
  refine ⟨min epsilonD epsilonB, lt_min hDpos hBpos,
    (min_le_left _ _).trans hDsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q
  let a := (D₀.scalarCurvature q)⁻¹
  obtain ⟨D⟩ := hdata H T (hepsilon.trans (min_le_left _ _)) A1 hA1 phi G D₀ q
  have ha : 0 < a := D.scale_pos
  obtain ⟨B, hB, hsource⟩ := hbounds epsilon (D.neck 0).epsilon_pos
    (hepsilon.trans (min_le_right _ _))
  have hbound (k : ℕ) := hsource (E (D.sourceIndex k + H.shift)).flow
    (E (D.sourceIndex k + H.shift)).time (D.neck k) (D.raw k)
    ((E (D.sourceIndex k + H.shift)).flow.scalar
      ⟨(E (D.sourceIndex k + H.shift)).time, (E (D.sourceIndex k + H.shift)).basepoint⟩)
    (H.base_scalar_pos (D.sourceIndex k)) (a / 2) (half_pos ha) (D.scale_lower k)
    (a / 8) (by linarith) (D.common_window k)
  refine ⟨D, ⟨K / (a / 2), div_pos hK (half_pos ha), ?_⟩, ?_⟩
  · intro k t ht x
    exact (hbound k).1 t ht x
  · intro m
    refine ⟨(Real.sqrt (a / 2))⁻¹ ^ (m + 2) * B m, ?_, ?_⟩
    · exact mul_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (half_pos ha))) _) (hB m)
    intro k t ht x hx
    apply (hbound k).2 m t ht (D.parametrization k x)
    have hpoint : (D.parametrization k x).val = (D.sourceMap k ⟨x, hx⟩).val.val := by
      rw [show D.parametrization k x = D.neckMap k ⟨x, hx⟩ from
        D.parametrization_apply k ⟨x, hx⟩]
      rfl
    rw [hpoint]
    exact D.sourceMap_mem_ball k ⟨x, hx⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
