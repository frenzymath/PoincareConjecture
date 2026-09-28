import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckBufferedNeighborhood
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallChartCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshCapture
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactOpenDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 1600000 in

theorem eventually_retained_whole_neighborhood_in_core
    {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)}
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (hsmall : epsilon ≤ 1 / 10000)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric), L.epsilon = 3 * epsilon / 2 →
      ∀ (sigma : ℕ → ℕ), StrictMono sigma →
      ∀ (N : ∀ k, EpsilonNeck
        ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.metric
          (E (W.high_index (G.subsequence (sigma k)) + H.shift)).time)),
        (∀ k, (N k).epsilon = epsilon) →
        (∀ k, (N k).center = (G.embedding (sigma k) L.center).val.val) →
        (∀ᶠ k in atTop, (9 / 10 : ℝ) * L.scale ≤ Real.sqrt
          ((E (W.high_index (G.subsequence (sigma k)) + H.shift)).flow.scalar
            ⟨(E (W.high_index (G.subsequence (sigma k)) + H.shift)).time,
              (E (W.high_index (G.subsequence (sigma k)) + H.shift)).basepoint⟩) *
                (N k).scale) →
        ∀ᶠ k in atTop, ∀ y ∈ L.carrier,
          |(L.coordinate_inverse y).2| ≤ 3 * epsilon⁻¹ / 5 →
          (G.embedding (sigma k) y).val.val ∈ (N k).carrier ∧
            |((N k).coordinate_inverse (G.embedding (sigma k) y).val.val).2| <
              3 * epsilon⁻¹ / 4 := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  intro L hL sigma hsigma N heps hcenter hfloor
  have hepsilon : 0 < epsilon := heps 0 ▸ (N 0).epsilon_pos
  have hinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have heta : L.epsilon < 8 * epsilon / 5 := by rw [hL]; linarith
  have hetahalf : 8 * epsilon / 5 < 1 / 2 := by linarith
  let R := L.restrict_m28 (8 * epsilon / 5) heta.le hetahalf
  let U : TopologicalSpace.Opens G.limitCarrier.carrier := ⟨R.carrier, R.carrier_open⟩
  have hU : IsCompact (closure (U : Set G.limitCarrier.carrier)) :=
    (L.restrict_compactClosure heta hetahalf).1
  have hc : L.center ∈ (U : Set G.limitCarrier.carrier) :=
    R.central_sphere_subset R.center_on_central_sphere
  have hwidth : (8 * epsilon / 5)⁻¹ = 5 * epsilon⁻¹ / 8 := by
    field_simp
  have hmetric := hsigma.tendsto_atTop.eventually
    (G.eventually_compact_open_edist_le U hU (101 / 100) (by norm_num))
  filter_upwards [hmetric, hfloor] with k hk hkfloor
  intro y hy hheight
  have hyU : y ∈ (U : Set G.limitCarrier.carrier) := by
    refine ⟨hy, ?_⟩
    rw [hwidth]
    exact abs_lt.mp (hheight.trans_lt (by linarith))
  have hlimit : (intrinsicOpenMetric G.limitMetric U).edist ⟨L.center, hc⟩ ⟨y, hyU⟩ <
      ENNReal.ofReal ((61 / 100 : ℝ) * L.scale * epsilon⁻¹) := by
    rw [intrinsicOpenMetric_edist]
    exact L.buffered_intrinsicEDist_lt hepsilon hsmall hL hy hheight
  have hdist := (hk ⟨L.center, hc⟩ ⟨y, hyU⟩).trans_lt
    (ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (101 / 100 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top hlimit)
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 101 / 100)] at hdist
  have hnum : (101 / 100 : ℝ) * (61 / 100 * L.scale * epsilon⁻¹) <
      (62 / 100 : ℝ) * L.scale * epsilon⁻¹ := by
    nlinarith only [mul_pos L.scale_pos hinv]
  have hshort := hdist.trans ((ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (mul_pos (by norm_num) L.scale_pos) hinv)).mpr hnum)
  let nu := W.high_index (G.subsequence (sigma k))
  let Q := (E (nu + H.shift)).flow.scalar
    ⟨(E (nu + H.shift)).time, (E (nu + H.shift)).basepoint⟩
  have hroot : (999 / 1000 : ℝ) ≤ Real.sqrt (1 - epsilon) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hproduct : ((9 / 10 : ℝ) * L.scale) * (999 / 1000) ≤
      (Real.sqrt Q * (N k).scale) * Real.sqrt (1 - epsilon) :=
    mul_le_mul hkfloor hroot (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) (N k).scale_pos.le)
  have hscaled := mul_le_mul_of_nonneg_right hproduct
    (show 0 ≤ 3 * epsilon⁻¹ / 4 by positivity)
  have hradius : (62 / 100 : ℝ) * L.scale * epsilon⁻¹ ≤
      Real.sqrt Q * (((N k).scale * Real.sqrt (1 - (N k).epsilon)) *
        (3 * epsilon⁻¹ / 4)) := by
    rw [heps k]
    nlinarith only [hscaled, mul_pos L.scale_pos hinv]
  have hball := H.tubeCritical_mem_original_ball W.tube W.radius nu
    (G.embedding (sigma k) L.center) (G.embedding (sigma k) y)
    (((N k).scale * Real.sqrt (1 - (N k).epsilon)) * (3 * epsilon⁻¹ / 4))
    (hshort.trans_le (ENNReal.ofReal_le_ofReal hradius))
  rw [← hcenter k] at hball
  have hsourceCenter := (N k).central_sphere_subset (N k).center_on_central_sphere
  have hzero : ((N k).coordinate_inverse (N k).center).2 = 0 :=
    (((N k).mem_central_sphere_iff (N k).center).mp (N k).center_on_central_sphere).2
  have hinside := (N k).ball_subset_centered_region hsourceCenter
    (show 0 < 3 * epsilon⁻¹ / 4 by positivity)
    (by rw [heps k, hzero, abs_zero]; linarith) hball
  refine ⟨hinside.1, abs_lt.mpr ?_⟩
  simpa only [hzero, zero_sub, zero_add] using hinside.2

end PoincareConjecture.M28.CounterexampleNeckFamily
