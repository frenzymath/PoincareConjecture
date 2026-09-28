import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ScalarConvergence
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCenteredNecks
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar

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

theorem tubeCritical_scalar_eq (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (k : ℕ)
    (D : LeviCivitaData (H.tubeCriticalMetric T A1 k))
    (x : H.tubeCriticalRegion T A1 k) :
    D.scalarCurvature x =
      (E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, x.val.val⟩ /
        (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ := by
  rw [intrinsicOpenMetric_scalarCurvature (H.tubeMetric T k)
    (H.tubeCriticalRegion T A1 k) D (H.tubeConnection T k) x,
    H.tube_scalar_eq, H.normalizedSlice_scalar_eq]

theorem exists_source_criticalBall_scalar_lower_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ (A1 : ℝ) (k : ℕ)
          (D : LeviCivitaData (H.tubeCriticalMetric T A1 k))
          (x : H.tubeCriticalRegion T A1 k),
          8 * (max C 2) ^ 2 ≤ D.scalarCurvature x := by
  obtain ⟨epsilon₀, hpos, hsmall, hregion⟩ := exists_source_neck_region_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 k D x
  have h := ((hregion (E (k + H.shift)) (H.segment k)
    (H.base_scalar_pos k) hepsilon).2.2 x.val.val
      ((T k).carrier_subset_neckCarrierUnion x.val.property)).1
  rw [H.tubeCritical_scalar_eq T A1 k D x]
  exact (le_div_iff₀ (H.base_scalar_pos k)).mpr h

theorem exists_source_criticalBall_limit_scalar_lower_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
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
          ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
            8 * (max C 2) ^ 2 ≤ D₀.scalarCurvature q := by
  obtain ⟨epsilon₀, hpos, hsmall, hlower⟩ :=
    exists_source_criticalBall_scalar_lower_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hA1 phi G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q
  let D (k : ℕ) : LeviCivitaData (H.tubeCriticalMetric T A1 (phi k)) :=
    Classical.choice (exists_leviCivitaData (H.tubeCriticalMetric T A1 (phi k)))
  exact G.scalarCurvature_lower_bound D D₀ q _ (Eventually.of_forall
    (fun k => hlower H T hepsilon A1 (phi (G.subsequence k))
      (D (G.subsequence k)) (G.embedding k q)))

theorem source_centered_neck_scale_sq_eq_inverse_scalar
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    (A1 : ℝ) (k : ℕ) (D : LeviCivitaData (H.tubeCriticalMetric T A1 k))
    (x : H.tubeCriticalRegion T A1 k)
    (J : GeneralizedStrongNeck (E (k + H.shift)).flow (E (k + H.shift)).time epsilon)
    (hcenter : J.center = x.val.val) (hepsilon : epsilon < 1 / 2) :
    (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ * J.scale ^ 2 =
      (D.scalarCurvature x)⁻¹ := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hcenterNorm := tube.neck_normalized_scalar_center
    (strongNeck_top J hepsilon)
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
  change J.scale ^ 2 * (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, J.center⟩ = 1 at hcenterNorm
  have hnormalized : (Q * J.scale ^ 2) * D.scalarCurvature x = 1 := by
    rw [H.tubeCritical_scalar_eq T A1 k D x, ← hcenter]
    change (Q * J.scale ^ 2) *
      ((E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, J.center⟩ / Q) = 1
    calc
      _ = J.scale ^ 2 * (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, J.center⟩ := by field_simp
      _ = 1 := hcenterNorm
  exact eq_inv_of_mul_eq_one_left hnormalized

end PoincareConjecture.M28.CounterexampleNeckFamily
