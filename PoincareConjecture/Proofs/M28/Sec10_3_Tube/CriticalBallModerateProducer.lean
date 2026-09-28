import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallMarginOrScale
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundaryTransport
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open PoincareConjecture.EpsilonNeck

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

private theorem chain_neck_eq_list_node
    (H : CounterexampleNeckFamily E) {k : ℕ}
    (T : SourceTubeData (H.segment k)) {i : ℤ}
    (_hi : i ∈ (T.chain.shape.active)) :
    T.chain.neck i = (T.list.node i).2 := by
  rw [T.neck_eq]
  exact T.list.neckOfList_eq_node i

private theorem normalized_ball_original_edist_lt
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {k : ℕ} {i : ℤ}
    {delta : ℝ}
    (_hi : i ∈ (T k).chain.shape.active)
    {x y : (T k).carrierOpen}
    (hy : y ∈ (H.tubeMetric T k).ball x (delta / 48)) :
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).edist
        x.1 y.1 <
      ENNReal.ofReal
        ((delta / 48) / Real.sqrt
          ((E (k + H.shift)).flow.scalar
            ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩)) := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hball : (H.tubeMetric T k).edist x y < ENNReal.ofReal (delta / 48) := hy
  have hambient : (H.normalizedSliceMetric k).edist x.1 y.1 ≤
      (H.tubeMetric T k).edist x y := by
    rw [tubeMetric, intrinsicOpenMetric_edist] at hball ⊢
    exact RiemannianMetric.edist_le_intrinsicEDist
      (H.normalizedSliceMetric k) (T k).carrierOpen x.1 y.1
  have hnorm : (H.normalizedSliceMetric k).edist x.1 y.1 <
      ENNReal.ofReal (delta / 48) := hambient.trans_lt hball
  have hhom := M13.homothety_edist
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    (H.normalizedSliceMetric k) (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
    (M13.identity_metricHomothety _ Q hQ) x.1 y.1
  have hprod : ENNReal.ofReal (Real.sqrt Q) *
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).edist x.1 y.1 <
      ENNReal.ofReal (delta / 48) := by
    rw [← hhom]
    exact hnorm
  by_contra hnot
  have hge : ENNReal.ofReal ((delta / 48) / Real.sqrt Q) ≤
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).edist x.1 y.1 :=
    le_of_not_gt hnot
  have hmul := mul_le_mul_left hge (ENNReal.ofReal (Real.sqrt Q))
  have hreal : Real.sqrt Q * ((delta / 48) / Real.sqrt Q) = delta / 48 := by
    field_simp
  have hmul' : ENNReal.ofReal (delta / 48) ≤
      ENNReal.ofReal (Real.sqrt Q) *
        ENNReal.ofReal ((delta / 48) / Real.sqrt Q) := by
    rw [← ENNReal.ofReal_mul (le_of_lt hsqrt), hreal]
  exact (not_lt_of_ge (hmul'.trans (by simpa [mul_comm] using hmul))) hprod

theorem exists_criticalBall_moderate_witness_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ →
        ∀ {A1 delta : ℝ} {k : ℕ}
          (x : H.tubeCriticalRegion T A1 k) {i : ℤ},
          i ∈ (T k).chain.shape.active →
          (x : (T k).carrierOpen).val ∈ ((T k).chain.neck i).carrier →
          |(((T k).chain.neck i).coordinate_inverse
              (x : (T k).carrierOpen).val).2| ≤
            3 * ((T k).chain.neck i).epsilon⁻¹ / 4 →
          0 < delta →
          delta / 48 ≤ H.tubeNodeScale T k i →
          CriticalBallModerateWitness H T (A1 := A1) (delta := delta) k x := by
  obtain ⟨epsilonS, hSpos, hSsmall, hS⟩ :=
    tube.exists_cylinder_scalar_accuracy.{u} (delta := 1 / 100) (by norm_num)
  let epsilon₀ := min (1 / 200 : ℝ) epsilonS
  refine ⟨epsilon₀, lt_min (by norm_num) hSpos, min_le_left _ _, ?_⟩
  intro epsilon C A E H T hsmall A1 delta k x i hi hx hquarter hdelta hscale
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let N := (T k).chain.neck i
  have hN : N.epsilon = epsilon := by
    dsimp [N]
    exact (T k).chain.epsilon_eq i hi
  have hNsmall : N.epsilon ≤ epsilonS := by
    rw [hN]
    exact hsmall.trans (min_le_right _ _)
  have hnode : N = ((T k).list.node i).2 := chain_neck_eq_list_node H (T k) hi
  have hscale' : delta / 48 ≤ Real.sqrt Q * N.scale := by
    simpa only [tubeNodeScale, hnode] using hscale
  have hquarter' : |(N.coordinate_inverse (x : (T k).carrierOpen).val).2| ≤
      3 * N.epsilon⁻¹ / 4 := by
    simpa only [N] using hquarter
  have hball : (H.tubeMetric T k).ball (x : (T k).carrierOpen) (delta / 48) ⊆
      (Subtype.val : (T k).carrierOpen → _) ⁻¹' N.carrier := by
    intro y hy
    have hxy := normalized_ball_original_edist_lt H T hi hy
    have hr : 0 < N.epsilon⁻¹ / 8 := by
      exact div_pos (inv_pos.mpr N.epsilon_pos) (by norm_num)
    have hmargin : N.epsilon⁻¹ / 8 < N.epsilon⁻¹ -
        |(N.coordinate_inverse (x : (T k).carrierOpen).val).2| := by
      have hepsinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
      have hquarter'' := hquarter'
      nlinarith
    have hroot : (1 / 2 : ℝ) < Real.sqrt (1 - N.epsilon) := by
      have hnonneg : 0 ≤ 1 - N.epsilon := by
        have : N.epsilon ≤ (1 / 200 : ℝ) := hNsmall.trans hSsmall
        linarith
      have hsquare : (Real.sqrt (1 - N.epsilon)) ^ 2 = 1 - N.epsilon :=
        Real.sq_sqrt hnonneg
      have hpos : 0 < Real.sqrt (1 - N.epsilon) := Real.sqrt_pos.mpr (by linarith)
      nlinarith
    have hfactor : 1 < Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8) := by
      have hepsinv : 200 ≤ N.epsilon⁻¹ := by
        have heps200 : N.epsilon ≤ (1 / 200 : ℝ) := hNsmall.trans hSsmall
        have hinv : (1 / 200 : ℝ)⁻¹ ≤ N.epsilon⁻¹ :=
          (inv_le_inv₀ (by norm_num : (0 : ℝ) < 1 / 200) N.epsilon_pos).2 heps200
        norm_num at hinv ⊢
        exact hinv
      nlinarith
    have hthreshold : delta / 48 <
        Real.sqrt Q * (N.scale * Real.sqrt (1 - N.epsilon) *
          (N.epsilon⁻¹ / 8)) := by
      have hnonneg : 0 ≤ Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_right hscale' hnonneg
      have hstrict : delta / 48 < (delta / 48) *
          (Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8)) := by
        nlinarith
      calc
        delta / 48 < (delta / 48) *
            (Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8)) := hstrict
        _ ≤ (Real.sqrt Q * N.scale) *
            (Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8)) := hmul
        _ = Real.sqrt Q * (N.scale * Real.sqrt (1 - N.epsilon) *
            (N.epsilon⁻¹ / 8)) := by ring
    apply mem_carrier_of_edist_lt_escape N (x := (x : (T k).carrierOpen).val)
      (y := y.val) hx hr hmargin
    have hQroot : 0 ≤ Real.sqrt Q := (Real.sqrt_pos.mpr hQ).le
    have hleft : ENNReal.ofReal (Real.sqrt Q) *
        ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).edist
          (x : (T k).carrierOpen).val y.val <
        ENNReal.ofReal (delta / 48) := by
      have hxy := normalized_ball_original_edist_lt H T hi hy
      have hscaled := ENNReal.mul_lt_mul_left
        (a := ENNReal.ofReal (Real.sqrt Q))
        (b := ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).edist
          (x : (T k).carrierOpen).val y.val)
        (c := ENNReal.ofReal ((delta / 48) / Real.sqrt Q))
        (ENNReal.ofReal_pos.mpr hsqrt).ne' ENNReal.ofReal_ne_top hxy
      calc
        ENNReal.ofReal (Real.sqrt Q) *
            ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).edist
              (x : (T k).carrierOpen).val y.val <
            ENNReal.ofReal (Real.sqrt Q) *
              ENNReal.ofReal ((delta / 48) / Real.sqrt Q) := by
          simpa [mul_comm] using hscaled
        _ = ENNReal.ofReal (delta / 48) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
          field_simp
    have hprod : ENNReal.ofReal (Real.sqrt Q) *
        ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
          (N.epsilon⁻¹ / 8)) > ENNReal.ofReal (delta / 48) := by
      rw [← ENNReal.ofReal_mul hQroot]
      have hfactorpos : 0 < N.scale * Real.sqrt (1 - N.epsilon) *
          (N.epsilon⁻¹ / 8) := by
        exact mul_pos (mul_pos N.scale_pos (by linarith [hroot])) hr
      have hfullpos : 0 < Real.sqrt Q *
          (N.scale * Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ / 8)) :=
        mul_pos hsqrt hfactorpos
      exact (ENNReal.ofReal_lt_ofReal_iff hfullpos).mpr hthreshold
    by_contra hnot
    have hge : ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) *
        (N.epsilon⁻¹ / 8)) ≤
        ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).edist
          (x : (T k).carrierOpen).val y.val := le_of_not_gt hnot
    exact (not_lt_of_ge (by
      simpa [mul_comm] using
        (mul_le_mul_left hge (ENNReal.ofReal (Real.sqrt Q)))))
      (hleft.trans hprod)
  have haccuracy : ∀ y ∈ (Subtype.val : (T k).carrierOpen → _) ⁻¹' N.carrier,
      |H.tubeNodeScale T k i ^ 2 *
          (H.tubeConnection T k).scalarCurvature y - 1| < (1 / 100 : ℝ) := by
    intro y hy
    have hyN : y.val ∈ N.carrier := hy
    have h := hS ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
      ((E (k + H.shift)).flow.connection (E (k + H.shift)).time) N hNsmall
      y.val hyN
    change |N.scale ^ 2 * (E (k + H.shift)).flow.scalar
        ⟨(E (k + H.shift)).time, y.val⟩ - 1| < (1 / 100 : ℝ) at h
    have hscalar := H.tube_scalar_eq T k y
    have hnormalized := H.normalizedSlice_scalar_eq k y.val
    have hscaleQ : H.tubeNodeScale T k i = Real.sqrt Q * N.scale := by
      simp only [tubeNodeScale, hnode, Q]
    rw [hscaleQ, hscalar, hnormalized]
    change |(Real.sqrt Q * N.scale) ^ 2 *
        ((E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, y.val⟩ / Q) - 1| < (1 / 100 : ℝ)
    have hcancel : (Real.sqrt Q * N.scale) ^ 2 *
        ((E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, y.val⟩ / Q) =
        N.scale ^ 2 * (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, y.val⟩ := by
      rw [mul_pow, Real.sq_sqrt hQ.le]
      field_simp [hQ.ne']
    rw [hcancel]
    exact h
  refine ⟨i, hi, hx, hquarter, hscale, hball, haccuracy⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
