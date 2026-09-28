import PoincareConjecture.Proofs.M47.LimitNoncollapseCompactDiameter
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime
import PoincareConjecture.Proofs.M47.LimitNoncollapsePointScalar
import PoincareConjecture.Proofs.M47.LimitNoncollapsePointDistance
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

private theorem normalized_distance_lt_scalar_radius
    {Q R c d B A : ℝ} (hQ : 0 < Q) (hR : 0 < R) (hc : 0 < c) (hd : 0 ≤ d)
    (hscalar : R / Q < 2 * c) (hdist : Real.sqrt Q * d < B)
    (hA : B * Real.sqrt (2 * c) < A) : d < A * R ^ (-1 / 2 : ℝ) := by
  have hroot : Real.sqrt R ≤ Real.sqrt (2 * c) * Real.sqrt Q := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * c)]
    exact Real.sqrt_le_sqrt ((div_lt_iff₀ hQ).mp hscalar).le
  have hproduct : d * Real.sqrt R < A := by
    calc
      _ ≤ d * (Real.sqrt (2 * c) * Real.sqrt Q) :=
        mul_le_mul_of_nonneg_left hroot hd
      _ = Real.sqrt (2 * c) * (Real.sqrt Q * d) := by ring
      _ < Real.sqrt (2 * c) * B := mul_lt_mul_of_pos_left hdist (by positivity)
      _ = B * Real.sqrt (2 * c) := mul_comm _ _
      _ < A := hA
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  exact (lt_div_iff₀ (Real.sqrt_pos.mpr hR)).mpr hproduct

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

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitFinite_compact_scalar_bound
    (P : M47Predecessors.{u}) (schedules : RepairedControlledSchedulesData.{u})
    (hH : 0 < H) (hfinite : H ≠ ⊤) {epsilon C : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon₀ : epsilon ≤ schedules.calibration.epsilon₁₀)
    (hC : 0 < C)
    (hParameters : ∀ k, (F k).parameters.epsilon = epsilon ∧ (F k).parameters.C = C)
    (hPinched : ∀ k, ∀ s ∈ (W k).interval, SurgeryPinchedAt ((F k).connection s) s)
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    {B0 : ℝ} (hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0)
    {X : Set G.limit.carrier.carrier} (hX : IsCompact X) (hXconnected : IsPreconnected X)
    {c : ℝ} (hlow : ∀ t ∈ blowupBackwardInterval H,
      ∃ y ∈ X, (G.limit.flow.connection t).scalarCurvature y ≤ c) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t ∈ blowupBackwardInterval H, ∀ z ∈ X,
      (G.limit.flow.connection t).scalarCurvature z ≤ K := by
  classical
  let c0 := max c 2 + 1
  have hc : c < c0 := by dsimp only [c0]; linarith [le_max_left c 2]
  have hc2 : 2 < c0 := by dsimp only [c0]; linarith [le_max_right c 2]
  have hc0 : 0 < c0 := by linarith
  obtain ⟨DX, hDX, hdiam⟩ :=
    limitFinite_compact_diameter P.m04 hH hfinite G.limit hterminal hX
  let A := 2 * (DX + 1) * Real.sqrt (2 * c0) + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  obtain ⟨D0, D, hD0, hD, hEstimate⟩ :=
    exists_regular_history_bounded_distance schedules epsilon hepsilon hepsilon₀ C hC A hA.le
  let K := max 1 (max c0 (4 * c0 * D))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro t ht z hz
  by_contra hnot
  have hhigh : K < (G.limit.flow.connection t).scalarCurvature z := lt_of_not_ge hnot
  have hc0z : c0 < (G.limit.flow.connection t).scalarCurvature z :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hhigh
  have hDz : 4 * c0 * D < (G.limit.flow.connection t).scalarCurvature z :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hhigh
  have hRz : 0 < (G.limit.flow.connection t).scalarCurvature z := hc0.trans hc0z
  obtain ⟨y0, hy0, hRy0⟩ := hlow t ht
  have hcont := (P.m04.tensor_calculus 3 G.limit.carrier.carrier
    (G.limit.flow.metric t) (G.limit.flow.connection t)).contMDiff_scalarCurvature.continuous
  obtain ⟨y, hy, hRy⟩ := hXconnected.intermediate_value hy0 hz hcont.continuousOn
    ⟨hRy0.trans hc.le, hc0z.le⟩
  have hyTail := limitNoncollapse_eventually_point_scalar G P t ht y (half_pos hc0)
  have hzTail := limitNoncollapse_eventually_point_scalar G P t ht z (half_pos hRz)
  have hdTail := limitNoncollapse_eventually_point_distance G t ht y z zero_lt_one
  have htTail := limitNoncollapse_eventually_physical_time_pos hfinite G
    (fun k => regular_history_interval_nonnegative (history k)) t ht
  have hqTail : ∀ᶠ k : ℕ in atTop, 2 * D0 / c0 ≤ (V).scale (G.subsequence k) :=
    ((V).scalar_diverges.comp G.subsequence_strictMono.tendsto_atTop).eventually
      (eventually_ge_atTop (2 * D0 / c0))
  obtain ⟨k, hky, hkz, hkd, hkt, hkq⟩ :=
    (hyTail.and (hzTail.and (hdTail.and (htTail.and hqTail)))).exists
  let hs := hky.1
  let q := (V).scale (G.subsequence k)
  let tau := ((V).base (G.subsequence k)).1 + t / q
  let yk := (G.embedding k).forward t hs y
  let zk := (G.embedding k).forward t hs z
  let Ry := ((V).flow (G.subsequence k)).scalar ⟨tau, yk⟩
  let Rz := ((V).flow (G.subsequence k)).scalar ⟨tau, zk⟩
  have hq : 0 < q := (G.embedding k).scale_pos
  have hRyErr : |Ry / q - c0| < c0 / 2 := by
    have herr := hky.2.2 hs
    change |Ry / q - (G.limit.flow.connection t).scalarCurvature y| < c0 / 2 at herr
    rwa [hRy] at herr
  have hRzErr : |Rz / q - (G.limit.flow.connection t).scalarCurvature z| <
      (G.limit.flow.connection t).scalarCurvature z / 2 := hkz.2.2 hs
  have hyLower : c0 / 2 < Ry / q := by linarith [(abs_lt.mp hRyErr).1]
  have hyUpper : Ry / q < 2 * c0 := by linarith [(abs_lt.mp hRyErr).2]
  have hzLower : (G.limit.flow.connection t).scalarCurvature z / 2 < Rz / q := by
    linarith [(abs_lt.mp hRzErr).1]
  have hyLower' : (c0 / 2) * q < Ry := (lt_div_iff₀ hq).mp hyLower
  have hRypos : 0 < Ry := lt_trans (by positivity) hyLower'
  have hyLarge : D0 ≤ Ry := by
    have hq' : 2 * D0 ≤ q * c0 := (div_le_iff₀ hc0).mp hkq
    nlinarith
  have hcutoff : (rNext (G.subsequence k))⁻¹ ^ 2 ≤ 4 * Ry := by
    apply (hThreshold (G.subsequence k)).trans
    have hmult := mul_pos (show 0 < c0 - 2 by linarith) hq
    change q ≤ 4 * Ry
    nlinarith
  have htimeBase : tau ≤ baseTime (G.subsequence k) := by
    have hdiv := div_nonpos_of_nonpos_of_nonneg ht.1 hq.le
    change baseTime (G.subsequence k) + t / q ≤ baseTime (G.subsequence k)
    linarith
  have hphysicalCanonical : ∀ s ∈ (W (G.subsequence k)).interval, s < tau →
      s ∉ (F (G.subsequence k)).surgery_times →
      ∀ w : ((F (G.subsequence k)).slice s).carrier,
        4 * Ry ≤ ((F (G.subsequence k)).connection s).scalarCurvature w →
          SurgeryCanonicalControl (F (G.subsequence k)) s w epsilon C := by
    intro s hsw hst _hregular w hw
    have hsh : s ∈ (history (G.subsequence k)).generalized.interval :=
      (history (G.subsequence k)).interval_eq.symm ▸ hsw
    have hsF := (history (G.subsequence k)).history.time_subset hsh
    have hcanonical := hEarlier (G.subsequence k) s
      ⟨regular_history_interval_nonnegative (history (G.subsequence k)) hsh,
        hst.trans_le htimeBase⟩ hsF w (hcutoff.trans hw)
    simpa only [(hParameters (G.subsequence k)).1, (hParameters (G.subsequence k)).2]
      using hcanonical
  have hM28 := hEstimate (F (G.subsequence k)) (W (G.subsequence k))
    (history (G.subsequence k)) (hPinched (G.subsequence k)) tau hkt.2.1 hkt.2.2 yk
      hyLarge hphysicalCanonical
  have hsource := hkd.2.2.2 hs
  let gk := ((V).flow (G.subsequence k)).metric tau
  have hd : Real.sqrt q * (gk.edist yk zk).toReal < 2 * (DX + 1) := by
    have hdiameter := hdiam t ht y hy z hz
    exact hsource.2.trans_le (by linarith)
  have hradius : (gk.edist yk zk).toReal < A * Ry ^ (-1 / 2 : ℝ) :=
    normalized_distance_lt_scalar_radius hq hRypos hc0 ENNReal.toReal_nonneg
      hyUpper hd (by dsimp only [A]; linarith)
  have hzBall : zk ∈ gk.ball yk (A * Ry ^ (-1 / 2 : ℝ)) := by
    change gk.edist yk zk < ENNReal.ofReal _
    rw [← ENNReal.ofReal_toReal hsource.1]
    exact ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hradius)
      |>.mpr hradius
  have hratio : Rz ≤ D * Ry := hM28 zk hzBall
  have hratio' : Rz / q ≤ D * (Ry / q) := by
    simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right hratio hq.le)
  have hupper : Rz / q < D * (2 * c0) :=
    hratio'.trans_lt (mul_lt_mul_of_pos_left hyUpper hD)
  nlinarith

end PoincareConjecture.M47
