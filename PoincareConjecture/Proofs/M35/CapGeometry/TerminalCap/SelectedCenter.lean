import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.FineNeck
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.OriginalComparison
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedPointDistance
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedNeckTipDistance
import PoincareConjecture.Proofs.M35.Thm12_28.TerminalScalarConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => StandardCapSpace

theorem blowupSequence_separated_radial_center
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t : ℕ → ℝ) (x : ℕ → V)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa)
    {D J : ℝ} (hD : 0 ≤ D) (hJ : 0 < J)
    (hd : ∀ k, ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)) ≤ D) :
    ∃ y : L.limit.sliceCarrier.carrier, ∃ m U B : ℝ,
      0 < m ∧ 0 < U ∧ 0 < B ∧ ∀ᶠ k in atTop,
        let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
        let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
        let g := E.flow.metric (t (L.subsequence k))
        let G : RiemannianMetric 3 V := M13.scaleSmoothMetric g Q hQ
        let y' := ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val
        let R := (E.flow.connection (t (L.subsequence k))).scalarCurvature y'
        m * Q ≤ R ∧ R ≤ U * Q ∧
        J + radialArclength g ‖x (L.subsequence k)‖ * Real.sqrt R <
          radialArclength g ‖y'‖ * Real.sqrt R ∧
        G.edist (x (L.subsequence k)) y' < ENNReal.ofReal B := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  obtain ⟨B₀, hB₀, hscalarceil⟩ := blowupSequence_limit_scalar_ceiling P E t x ht hR L A
  let U := B₀ + 1
  have hU : 0 < U := by dsimp only [U]; positivity
  let K := J + D * Real.sqrt U + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨delta₁, hd₁, hneck⟩ := exists_limit_fine_neck P
  obtain ⟨delta₂, hd₂, htip⟩ := blowupSequence_selected_neck_tip_distance
  let delta := min delta₁ (min delta₂ (4 * K)⁻¹)
  have hdelta : 0 < delta := lt_min hd₁ (lt_min hd₂ (inv_pos.mpr (by positivity)))
  have hdsmall : delta ≤ delta₁ := min_le_left _ _
  have hdsmall₂ : delta ≤ delta₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hdinverse : 4 * K ≤ delta⁻¹ := by
    have hbound : delta ≤ (4 * K)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
    simpa only [inv_inv] using
      (inv_le_inv₀ (inv_pos.mpr (show 0 < 4 * K by positivity)) hdelta).mpr hbound
  obtain ⟨N, hNe, hND, hNc, j, hNj⟩ := hneck delta hdelta hdsmall E t x ht hR L A
  let y := N.center
  let r := (L.limit.flow.connection 0).scalarCurvature y
  have hr : 0 < r := by
    change 0 < (L.limit.flow.connection 0).scalarCurvature N.center
    rw [← hND]
    exact N.scalar_center_pos
  let m := r / 2
  have hm : 0 < m := half_pos hr
  have hrU : r < U := (hscalarceil y).trans_lt (by dsimp only [U]; linarith)
  have hscalar := blowupSequence_terminal_scalar_tendsto P E t x ht hR L y
  have hscalarlo := hscalar.eventually (eventually_gt_nhds (half_lt_self hr))
  have hscalarhi := hscalar.eventually (eventually_lt_nhds hrU)
  have htipfar := htip P E t x ht hR L N (hNe.symm ▸ hdsmall₂) hND hNc j hNj
  obtain ⟨B, hB, hdistance⟩ := blowupSequence_selected_point_distance_bound P E t x ht hR L y
  refine ⟨y, m, U, B, hm, hU, hB, ?_⟩
  filter_upwards [hscalarlo, hscalarhi, htipfar, hdistance] with k hlo hhi hfar hnear
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let g : RiemannianMetric 3 V := E.flow.metric (t (L.subsequence k))
  let hrot := E.rotation_invariant (t (L.subsequence k)) (ht _)
  let hc := E.complete (t (L.subsequence k)) (ht _)
  let y' := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val
  let R := (E.flow.connection (t (L.subsequence k))).scalarCurvature y'
  have hRpos : 0 < R := E.scalar_pos (ht _) y'
  have hlo' : m * Q ≤ R := (le_div_iff₀ hQ).mp hlo.le
  have hhi' : R ≤ U * Q := (div_le_iff₀ hQ).mp hhi.le
  have hbase : radialArclength g ‖x (L.subsequence k)‖ * Real.sqrt Q ≤ D := by
    have hh := hd (L.subsequence k)
    rw [edist_zero_eq_radialArclength g hrot hc P,
      ENNReal.toReal_ofReal (by
        simpa only [radialArclength_zero] using
          (radialArclength_strictMono g).monotone (norm_nonneg (x (L.subsequence k))))] at hh
    simpa only [Q, blowupSequence_scale] using hh
  have hradial : 0 ≤ radialArclength g ‖x (L.subsequence k)‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg (x (L.subsequence k)))
  have hsqrt : Real.sqrt R ≤ Real.sqrt U * Real.sqrt Q := by
    simpa only [Real.sqrt_mul hU.le] using Real.sqrt_le_sqrt hhi'
  have hbasenormal : radialArclength g ‖x (L.subsequence k)‖ * Real.sqrt R ≤
      D * Real.sqrt U := by
    calc
      _ ≤ radialArclength g ‖x (L.subsequence k)‖ * (Real.sqrt U * Real.sqrt Q) :=
        mul_le_mul_of_nonneg_left hsqrt hradial
      _ = (radialArclength g ‖x (L.subsequence k)‖ * Real.sqrt Q) * Real.sqrt U := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase (Real.sqrt_nonneg U)
  have hf : delta⁻¹ / 4 ≤ radialArclength g ‖y'‖ * Real.sqrt R := by
    rw [hNe] at hfar
    change delta⁻¹ / 4 ≤ (g.edist 0 y').toReal * Real.sqrt R at hfar
    rw [edist_zero_eq_radialArclength g hrot hc P,
      ENNReal.toReal_ofReal (by
        simpa only [radialArclength_zero] using
          (radialArclength_strictMono g).monotone (norm_nonneg y'))] at hfar
    exact hfar
  refine ⟨hlo', hhi', ?_, hnear⟩
  dsimp only [K] at hdinverse
  linarith only [hdinverse, hf, hbasenormal]

end PoincareConjecture.M35.OrdinaryRealization
