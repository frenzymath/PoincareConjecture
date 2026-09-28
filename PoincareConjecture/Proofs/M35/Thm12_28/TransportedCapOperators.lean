import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarOperators
import PoincareConjecture.Proofs.M35.Thm12_28.CapCompactness

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem three_halves_le_quadruple {S r : ℝ}
    (hS : 0 ≤ S) (hr : 0 ≤ r) (hSr : S ≤ 2 * r) :
    S ^ (3 / 2 : ℝ) ≤ 4 * r ^ (3 / 2 : ℝ) := by
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
    norm_num only [Real.rpow_two, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] at h
    exact h
  calc
    S ^ (3 / 2 : ℝ) ≤ (2 * r) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hS hSr (by norm_num)
    _ = 2 ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) := Real.mul_rpow (by norm_num) hr
    _ ≤ 4 * r ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hr _)

theorem blowupSequence_cap_scalar_operator_bounds (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (j : ℕ) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      ∃ k₀ : ℕ, j ≤ k₀ ∧ ∀ k ≥ k₀, ∀ y ∈ closure N.carrier,
        let z := ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val
        scalarGradientNorm (E.flow.metric (t (L.subsequence k)))
          (E.flow.connection (t (L.subsequence k))) z < 8 * N.cap_constant *
            (E.flow.connection (t (L.subsequence k))).scalarCurvature z ^ (3 / 2 : ℝ) ∧
        |(E.flow.connection (t (L.subsequence k))).laplacian
            (E.flow.connection (t (L.subsequence k))).scalarCurvature z +
              2 * (E.flow.connection (t (L.subsequence k))).ricciNormSq z| <
          8 * N.cap_constant * (E.flow.connection (t (L.subsequence k))).scalarCurvature z ^ 2 := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  intro N hconnection hcompact hU
  have hsmooth := Proofs.M09.scalarCurvature_contMDiff P.curvature N.connection
  have hscalar := hsmooth.continuous
  have hgradcont := continuous_scalarGradientNorm N.connection hsmooth
  have hevolcont : Continuous (fun y => N.connection.laplacian N.connection.scalarCurvature y +
      2 * N.connection.ricciNormSq y) := by
    simpa only [hconnection] using
      continuous_scalar_evolution_slice P L.limit.flow L.limit.zero_mem
  have hpower : Continuous (fun y => N.connection.scalarCurvature y ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp hscalar
  have hgrad : ∀ y ∈ closure N.carrier,
      scalarGradientNorm (L.limit.flow.metric 0) N.connection y ≤
        N.cap_constant * N.connection.scalarCurvature y ^ (3 / 2 : ℝ) := by
    obtain ⟨B, hB, hbound⟩ := N.gradient_bound
    apply closure_minimal
    · intro y hy
      exact (hbound y hy).trans (mul_le_mul_of_nonneg_right hB.le
        (Real.rpow_nonneg (N.scalar_pos y hy).le _))
    · exact isClosed_le hgradcont (continuous_const.mul hpower)
  have hevol : ∀ y ∈ closure N.carrier,
      |N.connection.laplacian N.connection.scalarCurvature y +
        2 * N.connection.ricciNormSq y| ≤ N.cap_constant * N.connection.scalarCurvature y ^ 2 := by
    obtain ⟨B, hB, hbound⟩ := N.laplacian_bound
    apply closure_minimal
    · intro y hy
      exact (hbound y hy).trans (mul_le_mul_of_nonneg_right hB.le (sq_nonneg _))
    · exact isClosed_le hevolcont.abs (continuous_const.mul (hscalar.pow 2))
  obtain ⟨a, _, ha, _, hfloor⟩ := N.exists_positive_scalar_bounds_on_closure hscalar
  let delta := min (N.cap_constant * a ^ (3 / 2 : ℝ)) (N.cap_constant * a ^ 2)
  have hdelta : 0 < delta := lt_min
    (mul_pos N.cap_constant_pos (Real.rpow_pos_of_pos ha _))
    (mul_pos N.cap_constant_pos (sq_pos_of_pos ha))
  obtain ⟨Ns, hjs, hs⟩ := blowupSequence_terminal_scalar_uniform_compact
    P E t x ht hR L j (closure N.carrier) hcompact hU (a / 2) (by positivity)
  obtain ⟨No, _, ho⟩ := blowupSequence_terminal_scalar_operators_uniform_compact
    P E t x ht hR L j (closure N.carrier) hcompact hU delta hdelta
  refine ⟨max Ns No, hjs.trans (le_max_left _ _), ?_⟩
  intro k hk y hy
  let z := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let R := (E.flow.connection (t (L.subsequence k))).scalarCurvature z
  let S := N.connection.scalarCurvature y
  let r := R / Q
  let G := scalarGradientNorm (E.flow.metric (t (L.subsequence k)))
    (E.flow.connection (t (L.subsequence k))) z / (Q * Real.sqrt Q)
  let O := ((E.flow.connection (t (L.subsequence k))).laplacian
    (E.flow.connection (t (L.subsequence k))).scalarCurvature z +
      2 * (E.flow.connection (t (L.subsequence k))).ricciNormSq z) / Q ^ 2
  let O₀ := N.connection.laplacian N.connection.scalarCurvature y +
    2 * N.connection.ricciNormSq y
  have hQ : 0 < Q := (L.embedding k).scale_pos
  have hS : a ≤ S := (hfloor y hy).1
  have hSpos : 0 < S := ha.trans_le hS
  have herr : |r - S| < a / 2 := by
    simpa only [r, S, R, Q, z, hconnection] using
      hs k ((le_max_left _ _).trans hk) y hy
  have hrpos : 0 < r := by linarith [(abs_lt.mp herr).1]
  have hSr : S ≤ 2 * r := by linarith [(abs_lt.mp herr).1]
  have hRpos : 0 < R := by
    simpa only [zero_mul] using (lt_div_iff₀ hQ).mp hrpos
  have herrors : |G - scalarGradientNorm (L.limit.flow.metric 0) N.connection y| < delta ∧
      |O - O₀| < delta := by
    simpa only [G, O, O₀, Q, z, hconnection] using
      ho k ((le_max_right _ _).trans hk) y hy
  have hdg : delta ≤ N.cap_constant * S ^ (3 / 2 : ℝ) :=
    (min_le_left _ _).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ha.le hS (by norm_num)) N.cap_constant_pos.le)
  have hde : delta ≤ N.cap_constant * S ^ 2 :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left
      (by nlinarith : a ^ 2 ≤ S ^ 2) N.cap_constant_pos.le)
  have hgradnorm : G < 8 * N.cap_constant * r ^ (3 / 2 : ℝ) := by
    have hg := hgrad y hy
    have hclose := (abs_lt.mp herrors.1).2
    have hpowerbound := mul_le_mul_of_nonneg_left
      (three_halves_le_quadruple hSpos.le hrpos.le hSr) N.cap_constant_pos.le
    nlinarith
  have hevolnorm : |O| < 8 * N.cap_constant * r ^ 2 := by
    have htriangle : |O| ≤ |O - O₀| + |O₀| := by
      simpa only [sub_add_cancel] using abs_add_le (O - O₀) O₀
    have hbound := hevol y hy
    have hsq : S ^ 2 ≤ 4 * r ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq N.cap_constant_pos.le
    linarith [herrors.2]
  have hQpow : Q ^ (3 / 2 : ℝ) = Q * Real.sqrt Q := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hQ,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  constructor
  · change _ < 8 * N.cap_constant * R ^ (3 / 2 : ℝ)
    apply (div_lt_div_iff_of_pos_right (mul_pos hQ (Real.sqrt_pos.2 hQ))).mp
    simpa only [G, r, Real.div_rpow hRpos.le hQ.le, hQpow, mul_div_assoc] using hgradnorm
  · change _ < 8 * N.cap_constant * R ^ 2
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hQ)).mp
    simpa only [O, r, abs_div, abs_of_pos (sq_pos_of_pos hQ), div_pow,
      mul_div_assoc] using hevolnorm

end PoincareConjecture.M35.OrdinaryRealization
