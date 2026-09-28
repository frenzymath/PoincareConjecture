import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.SelectedCenter
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.TwoCollars

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => StandardCapSpace

theorem blowupSequence_bounded_tip_radial_collars
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) (t : ℕ → ℝ) (x : ℕ → V)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) {kappa : ℝ}
    (A : BlowupAncientKappaIdentification L.limit kappa)
    {epsilon D : ℝ} (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) (hD : 0 ≤ D)
    (hd : ∀ k, ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k)) ≤ D) :
    ∃ Rmax F : ℝ, 0 < Rmax ∧ 0 < F ∧ ∀ᶠ k in atTop,
      ∃ N : RadialCapCollars E (t (L.subsequence k)) (ht _) epsilon,
        radialArclength (E.flow.metric (t (L.subsequence k))) ‖x (L.subsequence k)‖ <
          N.a - N.b * epsilon⁻¹ ∧
        (N.a + N.b * epsilon⁻¹) *
          Real.sqrt ((blowupSequence P E t x ht hR).scale (L.subsequence k)) ≤ Rmax ∧
        intrinsicWarpingRadius (E.flow.metric (t (L.subsequence k)))
          (E.rotation_invariant _ (ht _)) (E.complete _ (ht _)) N.a *
          Real.sqrt ((blowupSequence P E t x ht hR).scale (L.subsequence k)) ≤ F := by
  obtain ⟨T, hT, hcollars⟩ := exists_radial_cap_collars_threshold P E he hehalf
  let J := T + epsilon⁻¹ + 1
  have hel : 0 < epsilon⁻¹ := inv_pos.mpr he
  have hJ : 0 < J := by dsimp only [J]; positivity
  obtain ⟨y, m, U, B, hm, _hU, hB, hcenter⟩ :=
    blowupSequence_separated_radial_center P E t x ht hR L A hD hJ hd
  let rootm := Real.sqrt m
  have hrootm : 0 < rootm := Real.sqrt_pos.mpr hm
  let Rmax := D + B + rootm⁻¹ * epsilon⁻¹ + 1
  let F := 2 * rootm⁻¹
  have hRmax : 0 < Rmax := by dsimp only [Rmax]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hscale : Tendsto (fun k => (blowupSequence P E t x ht hR).scale (L.subsequence k))
      atTop atTop := by
    simpa only [blowupSequence_scale, Function.comp_def] using
      hR.comp L.subsequence_strictMono.tendsto_atTop
  refine ⟨Rmax, F, hRmax, hF, ?_⟩
  filter_upwards [hcenter, hscale.eventually_ge_atTop (T / m)] with k hk hlarge
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let g : RiemannianMetric 3 V := E.flow.metric (t (L.subsequence k))
  let G : RiemannianMetric 3 V := M13.scaleSmoothMetric g Q hQ
  let hrot := E.rotation_invariant (t (L.subsequence k)) (ht _)
  let hc := E.complete (t (L.subsequence k)) (ht _)
  let z := x (L.subsequence k)
  let y' := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val
  let R := (E.flow.connection (t (L.subsequence k))).scalarCurvature y'
  have hRpos : 0 < R := E.scalar_pos (ht _) y'
  have hrootR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have hrootQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  change m * Q ≤ R ∧ R ≤ U * Q ∧
    J + radialArclength g ‖z‖ * Real.sqrt R < radialArclength g ‖y'‖ * Real.sqrt R ∧
    G.edist z y' < ENNReal.ofReal B at hk
  have hhigh : T ≤ R := calc
    T = T / m * m := (div_mul_cancel₀ T hm.ne').symm
    _ ≤ Q * m := mul_le_mul_of_nonneg_right hlarge hm.le
    _ = m * Q := mul_comm _ _
    _ ≤ R := hk.1
  have hzrad : 0 ≤ radialArclength g ‖z‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg z)
  have hyrad : 0 ≤ radialArclength g ‖y'‖ := by
    simpa only [radialArclength_zero] using
      (radialArclength_strictMono g).monotone (norm_nonneg y')
  have hfar : T ≤ (g.edist 0 y').toReal * Real.sqrt R := by
    rw [edist_zero_eq_radialArclength g hrot hc P, ENNReal.toReal_ofReal hyrad]
    have hh := hk.2.2.1
    have hnonneg := mul_nonneg hzrad hrootR.le
    dsimp only [J] at hh
    linarith only [hh, hnonneg, hel]
  obtain ⟨N, hNa, hNb, _hNQ⟩ := hcollars (t (L.subsequence k)) (ht _) y' hhigh hfar
  have hbunit : N.b * Real.sqrt R = 1 := by rw [hNb]; exact inv_mul_cancel₀ hrootR.ne'
  have hbase : radialArclength g ‖z‖ < N.a - N.b * epsilon⁻¹ := by
    apply (mul_lt_mul_iff_of_pos_right hrootR).mp
    have hform : (N.a - N.b * epsilon⁻¹) * Real.sqrt R =
        N.a * Real.sqrt R - epsilon⁻¹ := by
      rw [sub_mul]
      congr 1
      calc
        _ = (N.b * Real.sqrt R) * epsilon⁻¹ := by ring
        _ = _ := by rw [hbunit, one_mul]
    rw [hform, hNa]
    have hh := hk.2.2.1
    dsimp only [J] at hh
    linarith only [hh, hT]
  have htip : G.edist 0 z ≤ ENNReal.ofReal D := by
    have heq := M13.homothety_edist g G (Diffeomorph.refl (𝓡 3) V ∞) Q hQ
      (M13.identity_metricHomothety g Q hQ) 0 z
    change G.edist 0 z = ENNReal.ofReal (Real.sqrt Q) * g.edist 0 z at heq
    have hh : (g.edist 0 z).toReal * Real.sqrt Q ≤ D := by
      simpa only [g, z, Q, blowupSequence_scale] using hd (L.subsequence k)
    rw [heq, ← ENNReal.ofReal_toReal (g.edist_ne_top 0 z),
      ← ENNReal.ofReal_mul hrootQ.le, mul_comm]
    exact ENNReal.ofReal_le_ofReal hh
  have hdistance : G.edist 0 y' ≤ ENNReal.ofReal (D + B) := calc
    _ ≤ G.edist 0 z + G.edist z y' :=
      @edist_triangle V G.toEMetricSpace.toPseudoEMetricSpace 0 z y'
    _ ≤ ENNReal.ofReal D + ENNReal.ofReal B := add_le_add htip hk.2.2.2.le
    _ = _ := (ENNReal.ofReal_add hD hB.le).symm
  have hNaQ : N.a * Real.sqrt Q ≤ D + B := by
    rw [edist_zero_eq_radialArclength G
      (scaleSmoothMetric_rotation_invariant hrot Q hQ)
      (scaleSmoothMetric_complete g hc Q hQ) P, radialArclength_scale] at hdistance
    have hh := (ENNReal.ofReal_le_ofReal_iff (add_nonneg hD hB.le)).mp hdistance
    rw [hNa]
    simpa only [mul_comm] using hh
  have hNbQ : N.b * Real.sqrt Q ≤ rootm⁻¹ := by
    have hsqrt : rootm * Real.sqrt Q ≤ Real.sqrt R := by
      simpa only [rootm, Real.sqrt_mul hm.le] using Real.sqrt_le_sqrt hk.1
    have h := mul_le_mul_of_nonneg_right hsqrt N.b_pos.le
    rw [mul_comm (Real.sqrt R), hbunit] at h
    have hh : (N.b * Real.sqrt Q) * rootm ≤ 1 := by nlinarith only [h]
    simpa only [one_div] using (le_div_iff₀ hrootm).mpr hh
  refine ⟨N, hbase, ?_, ?_⟩
  · have hw := mul_le_mul_of_nonneg_right hNbQ hel.le
    dsimp only [Rmax]
    nlinarith only [hNaQ, hw]
  · have hf := mul_lt_mul_of_pos_right N.radius hrootQ
    dsimp only [F]
    nlinarith only [hf, hNbQ]

end PoincareConjecture.M35.OrdinaryRealization
