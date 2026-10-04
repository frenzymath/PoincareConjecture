import PoincareLib.Geometry.RicciFlow.Surgery.Metric.OperationTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Profile.Constants
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Result
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Comparison.SurgeryComparison

/-!
# M36 metric-surgery proof entry

The constants are fixed before the manifold and input neck. The proof
assembles the actual local construction against the frozen metric-surgery
contract, including its closed collar and positive-surgery conclusions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

open MetricSurgery

/-
Morgan--Tian Claim 13.1 and Theorem 13.2 (printed pp. 332--333), together with
Lemma 13.4 (p. 334), state that universal constants and a large-q profile turn
any sufficiently small high-curvature epsilon-neck satisfying the pinching
conditions into a one-ended surgery output.  The output retains the negative
half-neck isometrically, supplies the cap chart and boundary/ball controls,
has positive cap curvature and transported pinching, admits the radial
collapse with intrinsic distance decrease, and is C^k-close to the fixed
standard initial metric at the requested comparison scale. The same collapse
sends the positive half-neck into the closed cap and is the actual cap tip
on a nonempty positive tail, as in Claim 13.1 (pp. 331--332). After fixing the
standard metric, the delta threshold is reduced before all neck inputs so
the cutoff A₀ + 4 lies strictly inside the neck. M36's public
contract quantifies only a primitive standard initial metric and every
admissible neck input; M34 and M35 are not theorem arguments.  The source audit
records that the radial collapse is used with its stated continuity and
intrinsic-distance properties rather than an unwarranted global smoothness or
ambient-distance claim.  The explicit profile-dominance field records the
source choice C₀ >> q, while the closed retained-isometry field includes the
central-sphere endpoint. If the input neck has positive sectional curvature
at every point, the entire output has positive sectional curvature, by
Corollary 13.12 and the proof of Theorem 13.2 (pp. 339--340). The threshold
is chosen uniformly before the neck, independently of its positive minimum.
The gluing construction on p. 331 and the identification in the proof of
Lemma 13.15 (p. 341) extend the same cap chart to the open radius-A₀+5
ball. Its closed radius-A₀+4 image is the closure of the original cap.
The same collapse and retained inverse are smooth on the neck collar
-epsilon^-1 < s < 1; their metric identity holds for s <= 0, including
the central sphere. No isometry on the positive collar or smoothness at
the radial-collapse locus is asserted. See the closed-collar contract in
reviews/contracts/2026-09-19-m36-closed-collar-contract.md.
-/
set_option maxHeartbeats 1000000 in
-- The assembly checks dependent metric and connection identities throughout.
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

end PoincareMT
