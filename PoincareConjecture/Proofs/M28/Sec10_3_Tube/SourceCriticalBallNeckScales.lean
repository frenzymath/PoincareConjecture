import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallScalarLimit










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 800000 in





theorem exists_source_criticalBall_neck_scale_limits_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ (A1 : ℝ) (hA1 : 0 < A1) (phi : ℕ → ℕ)
          (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric T A1 (phi k))
            (fun k => H.tubeCriticalBase T A1 hA1 (phi k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          let i := fun k => phi (G.subsequence k)
          let Q := fun k => (E (i k + H.shift)).flow.scalar
            ⟨(E (i k + H.shift)).time, (E (i k + H.shift)).basepoint⟩
          ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
            ∃ J : ∀ k, GeneralizedStrongNeck
                (E (i k + H.shift)).flow (E (i k + H.shift)).time epsilon,
              (∀ k, (J k).center = (G.embedding k q).val.val) ∧
              0 < (D₀.scalarCurvature q)⁻¹ ∧
              Tendsto (fun k => Q k * (J k).scale ^ 2) atTop
                (𝓝 (D₀.scalarCurvature q)⁻¹) ∧
              ∀ᶠ k in atTop,
                (D₀.scalarCurvature q)⁻¹ / 2 ≤ Q k * (J k).scale ^ 2 ∧
                  Q k * (J k).scale ^ 2 ≤ 2 * (D₀.scalarCurvature q)⁻¹ := by
  classical
  obtain ⟨epsilonN, hNpos, hNsmall, hnecks⟩ :=
    exists_source_tube_centered_strong_necks_accuracy P
  obtain ⟨epsilonR, hRpos, _hRsmall, hlower⟩ :=
    exists_source_criticalBall_limit_scalar_lower_accuracy.{u}
  refine ⟨min epsilonN epsilonR, lt_min hNpos hRpos,
    (min_le_left _ _).trans hNsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let i := fun k => phi (G.subsequence k)
  let Q := fun k => (E (i k + H.shift)).flow.scalar
    ⟨(E (i k + H.shift)).time, (E (i k + H.shift)).basepoint⟩
  dsimp only
  intro D₀ q
  have hepsN : epsilon ≤ epsilonN := hepsilon.trans (min_le_left _ _)
  have hepsR : epsilon ≤ epsilonR := hepsilon.trans (min_le_right _ _)
  have hepshalf : epsilon < 1 / 2 := (hepsN.trans hNsmall).trans_lt (by norm_num)
  have hneck (k : ℕ) : ∃ J : GeneralizedStrongNeck
      (E (i k + H.shift)).flow (E (i k + H.shift)).time epsilon,
      J.center = (G.embedding k q).val.val :=
    hnecks (E (i k + H.shift)) (H.segment (i k)) (H.base_scalar_pos (i k))
      hepsN (T (i k)) (G.embedding k q).val.val (G.embedding k q).val.property
  choose J hcenter using hneck
  let D (k : ℕ) : LeviCivitaData (H.tubeCriticalMetric T A1 k) :=
    Classical.choice (exists_leviCivitaData (H.tubeCriticalMetric T A1 k))
  have hR := G.tendsto_scalarCurvature (fun k => D (phi k)) D₀ q
  have hpositive : 0 < D₀.scalarCurvature q := by
    have hC : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    exact lt_of_lt_of_le (by positivity)
      (hlower H T hepsR A1 hA1 phi G D₀ q)
  have hinverse : 0 < (D₀.scalarCurvature q)⁻¹ := inv_pos.mpr hpositive
  have hscale (k : ℕ) : Q k * (J k).scale ^ 2 =
      ((D (i k)).scalarCurvature (G.embedding k q))⁻¹ :=
    H.source_centered_neck_scale_sq_eq_inverse_scalar T A1 (i k)
      (D (i k)) (G.embedding k q) (J k) (hcenter k) hepshalf
  have hconv : Tendsto (fun k => Q k * (J k).scale ^ 2) atTop
      (𝓝 (D₀.scalarCurvature q)⁻¹) := by
    simp_rw [hscale]
    exact hR.inv₀ hpositive.ne'
  refine ⟨J, hcenter, hinverse, hconv, ?_⟩
  have hnear := hconv.eventually (Ioo_mem_nhds (half_lt_self hinverse)
    (by linarith : (D₀.scalarCurvature q)⁻¹ < 2 * (D₀.scalarCurvature q)⁻¹))
  filter_upwards [hnear] with k hk
  exact ⟨hk.1.le, hk.2.le⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
