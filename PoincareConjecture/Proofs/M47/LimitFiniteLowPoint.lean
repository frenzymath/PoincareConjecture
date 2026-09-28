import PoincareConjecture.Proofs.M47.LimitFiniteLongSegment
import PoincareConjecture.Proofs.M47.LimitFiniteShrinkingNecks
import PoincareConjecture.Proofs.M47.LimitFiniteLimitReadout
import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteDistanceDyadic
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance finiteLowPointTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance finiteLowPointCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteLowPointManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold




theorem limitFinite_exists_fixed_low_point
    (P : M47Predecessors.{u}) (hH : 0 < H) (hfinite : H ≠ ⊤) {epsilon C : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hroundSmall : epsilon ≤ 1 / 200) (hC : 0 < C)
    (hParameters : ∀ k, (F k).parameters.epsilon = epsilon ∧ (F k).parameters.C = C)
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    {B0 : ℝ} (hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0)
    (hnoncompact : ¬IsCompact (univ : Set G.limit.carrier.carrier)) :
    ∃ (y : G.limit.carrier.carrier) (K : ℝ), 0 < K ∧
      ∀ t ∈ blowupBackwardInterval H, (G.limit.flow.connection t).scalarCurvature y ≤ K := by
  classical
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MeasurableSpace G.limit.carrier.carrier := G.limit.carrier.measurableSpace
  let : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
  let D := 80 * H.toReal * Real.sqrt (max 1 (3 * B0))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨y, z, d, hd, hoy, hyz, hoz⟩ := limitFinite_exists_long_terminal_segment
    (G.limit.flow.metric 0) (G.limit.complete 0 G.limit.zero_mem) hnoncompact G.limit.base hD
  suffices ∃ K : ℝ, 0 < K ∧ ∀ t ∈ blowupBackwardInterval H,
      (G.limit.flow.connection t).scalarCurvature y ≤ K from
    by obtain ⟨K, hK, hbound⟩ := this; exact ⟨y, K, hK, hbound⟩
  by_contra! hnot
  have hbad (n : ℕ) : ∃ t ∈ blowupBackwardInterval H,
      max ((n : ℝ) + 1) (3 * B0 + 1) <
        (G.limit.flow.connection t).scalarCurvature y :=
    hnot _ (lt_of_lt_of_le (by positivity) (le_max_left _ _))
  choose t ht hlarge using hbad
  have hhigh (n : ℕ) : 1 < (G.limit.flow.connection (t n)).scalarCurvature y := by
    have hn := (le_max_left ((n : ℝ) + 1) (3 * B0 + 1)).trans_lt (hlarge n)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hzero : (G.limit.flow.connection 0).scalarCurvature y ≤ 3 * B0 :=
    ((G.limit.flow.connection 0).scalarCurvature_le_curvatureTensorNorm_sharp y).trans
      (mul_le_mul_of_nonneg_left (hterminal y) (by norm_num))
  have hnegative (n : ℕ) : t n < 0 := by
    apply lt_of_le_of_ne (ht n).1
    intro hzeroTime
    have hn := (le_max_right ((n : ℝ) + 1) (3 * B0 + 1)).trans_lt (hlarge n)
    rw [hzeroTime] at hn
    linarith
  have hneck (n : ℕ) : ∃ N : EpsilonNeck (G.limit.flow.metric (t n)),
      N.connection = G.limit.flow.connection (t n) ∧ N.epsilon = 2 * epsilon ∧
      (G.limit.flow.connection (t n)).scalarCurvature y ≤
        (4 * max 1 C) * (G.limit.flow.connection (t n)).scalarCurvature N.center ∧
      (G.limit.flow.metric (t n)).edist y N.center < ENNReal.ofReal
        (4 * C * (G.limit.flow.connection (t n)).scalarCurvature y ^ (-1 / 2 : ℝ)) := by
    rcases limitFinite_nearby_neck_of_retained_convergence F W history baseTime hbaseTime
      basePoint hPositive hDiverges G P hfinite hepsilon hsmall hroundSmall hC
      hParameters rNext hThreshold hEarlier (t n) (ht n) (hnegative n) y (hhigh n)
      with h | h
    · exact h
    · exact False.elim (hnoncompact h)
  choose N hconnection heps hscalar hnear using hneck
  have hscalarDiverges : Tendsto
      (fun n => (G.limit.flow.connection (t n)).scalarCurvature y) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
      (fun n => ?_) tendsto_natCast_atTop_atTop
    have hn := (le_max_left ((n : ℝ) + 1) (3 * B0 + 1)).trans_lt (hlarge n)
    linarith
  have hA : 0 < 4 * max 1 C := mul_pos (by norm_num)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hcenterDiverges : Tendsto
      (fun n => (G.limit.flow.connection (t n)).scalarCurvature (N n).center)
      atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hscalarDiverges.eventually_ge_atTop ((4 * max 1 C) * b)] with n hn
    exact le_of_mul_le_mul_left (hn.trans (hscalar n)) hA
  have hrpow : Tendsto (fun s : ℝ => s ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have hscale : Tendsto (fun n => (N n).scale) atTop (𝓝 0) := by
    apply (hrpow.comp hcenterDiverges).congr'
    filter_upwards [] with n
    dsimp only [Function.comp_apply]
    rw [← hconnection n]
    exact (N n).scale_eq_scalar.symm
  have hnearUpper (n : ℕ) :
      ((G.limit.flow.metric (t n)).edist y (N n).center).toReal ≤
        4 * C * (G.limit.flow.connection (t n)).scalarCurvature y ^ (-1 / 2 : ℝ) := by
    have hpos := lt_trans zero_lt_one (hhigh n)
    simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ 4 * C * (G.limit.flow.connection (t n)).scalarCurvature y ^ (-1 / 2 : ℝ))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnear n).le
  have hnearTendsto : Tendsto
      (fun n => ((G.limit.flow.metric (t n)).edist y (N n).center).toReal)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hnearUpper
    simpa only [mul_zero, Function.comp_apply] using
      (hrpow.comp hscalarDiverges).const_mul (4 * C)
  have hsec (n : ℕ) : (N n).connection.NonnegativeSectionalCurvature := by
    rw [hconnection n]
    intro x
    exact LeviCivitaData.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      (G.limit.flow.connection (t n)) x (G.limit.nonnegative_curvature_operator (t n) (ht n) x)
  exact limitFinite_shrinking_necks_impossible (G.limit.flow.metric 0)
    (fun n => G.limit.flow.metric (t n)) N (fun n => G.limit.complete (t n) (ht n))
    hsec (by linarith : 2 * epsilon ≤ 1 / 100) heps G.limit.base y z hD hd hoy hyz hoz
    (fun n x w => limitFinite_additive_distance P.m04 hH hfinite G.limit hterminal
      (t n) (ht n) x w) hnearTendsto hscale

end PoincareConjecture.M47
