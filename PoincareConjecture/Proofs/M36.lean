import PoincareConjecture.Statements.M36MetricSurgery
import PoincareConjecture.Proofs.M36.Constants
import PoincareConjecture.Proofs.M36.SurgeryResult
import PoincareConjecture.Proofs.M36.SurgeryComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

open M36

set_option maxHeartbeats 1000000 in

theorem repairedMetricSurgery : RepairedMetricSurgeryTheory := by
  classical
  constructor
  intro g₀
  obtain ⟨r, hr, hrA, q0, hq0, hcurvature⟩ := exists_surgeryMetric_curvature g₀
  let q := max q0 101
  have hq100 : 100 < q := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hqA : 100 * (4 + g₀.cylindrical_end.radius) ^ 2 < q := by
    simpa only [add_comm] using hq0.trans_le (le_max_left q0 101)
  obtain ⟨C, hdominance, hcurvature⟩ := hcurvature q (le_max_left _ _)
  have hC : 0 < C := by linarith only [hq100, hdominance]
  obtain ⟨deltaC, hdeltaC, hcurvature⟩ := hcurvature C le_rfl
  choose comparison hcomparison hclose using fun eta : {e : ℝ // 0 < e} =>
    exists_surgeryMetric_standard_close g₀ C q hC.le hr eta.2
  let comparisonDelta : ℝ → ℝ := fun eta =>
    if heta : 0 < eta then comparison ⟨eta, heta⟩ else 1
  have hcomparisonDelta (eta : ℝ) (heta : 0 < eta) : 0 < comparisonDelta eta := by
    dsimp only [comparisonDelta]
    rw [dif_pos heta]
    exact hcomparison ⟨eta, heta⟩
  let upper := min deltaC (1 / (surgeryCapRadius g₀ * (6 + 2 * C)))
  have hupper : 0 < upper := lt_min hdeltaC (by
    have := surgeryCapRadius_pos g₀
    positivity)
  let K := profileConstants g₀ q C 1 upper comparisonDelta hq100 hdominance
    zero_lt_one hupper hcomparisonDelta
  have hprofile : SurgeryProfileLargeQ g₀ K := profileConstants_largeQ g₀ q C 1 upper
    comparisonDelta hq100 hdominance zero_lt_one hupper hcomparisonDelta hqA
  have hKupper : K.delta₀ ≤ upper := profileConstants_delta_le g₀ q C 1 upper
    comparisonDelta hq100 hdominance zero_lt_one hupper hcomparisonDelta
  refine ⟨{
    constants := K
    profile := hprofile
    profile_dominance := hdominance
    operation := ?_
  }⟩
  intro M _ _ _ _ _ _ _ _ g I
  have hcut : surgeryCapRadius g₀ < I.neck.epsilon⁻¹ := by
    simpa only [surgeryCapRadius, add_comm] using profileConstants_cutoff_inside
      g₀ q C 1 upper comparisonDelta hq100 hdominance zero_lt_one hupper
        hcomparisonDelta I.neck.epsilon_pos I.delta_le
  have hsize : I.neck.epsilon ≤ 1 / (surgeryCapRadius g₀ * (6 + 2 * K.C₀)) :=
    (I.delta_le.trans hKupper).trans (min_le_right _ _)
  have hcurvsmall : I.neck.epsilon ≤ deltaC :=
    (I.delta_le.trans hKupper).trans (min_le_left _ _)
  have hsmall : I.neck.epsilon < 1 / 200 := I.delta_le.trans_lt K.delta₀_lt
  have hetaN : 0 < 1 - 6 * I.neck.epsilon :=
    neck_contraction_coefficient_pos I.neck hsmall
  have hcurved := hcurvature (M := M) (g := g) I.neck hcut hcurvsmall
    I.neck.scalar_center_pos hetaN
  apply nonempty_metricSurgeryResult_of_curvature_comparison g₀ hprofile I hr hrA hcut hsize
  · dsimp only [K, profileConstants]
    exact hcurved
  · intro eta heta hepsilon
    have he : I.neck.epsilon ≤ comparison ⟨eta, heta⟩ := by
      simpa only [K, profileConstants, comparisonDelta, dif_pos heta] using hepsilon
    dsimp only [K, profileConstants]
    exact hclose ⟨eta, heta⟩ (M := M) (g := g) I.neck hcut hsmall he

end PoincareConjecture
