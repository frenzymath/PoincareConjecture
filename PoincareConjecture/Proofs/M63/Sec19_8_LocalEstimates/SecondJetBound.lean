import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.SecondJetDissipation
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ShortTimeFirstJet
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FiniteJetComparison
import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M04.FlowRiemannRegularity











set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

set_option maxHeartbeats 800000 in





theorem m63SecondJetSquared_bound_of_curvature_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {R delta : ℝ} (hR : 0 ≤ R) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ → ℝ → M, M62ShrinkingCurve F c →
      (∀ s ∈ Ioo a b, ∀ y, m63CurvatureJetSquared F c 0 s y ≤ R) →
      ∀ x t, t ∈ Ioo a b → delta ≤ t - a →
        m63CurvatureJetSquared F c 2 t x ≤ C := by
  have hab : a < b := by
    obtain ⟨s, hs, r, hr, hne⟩ := F.nontrivial
    by_contra! h
    exact hne (by linarith [hs.1, hs.2, hr.1, hr.2])
  let H := b - a
  have hH : 0 ≤ H := sub_nonneg.mpr hab.le
  by_cases hlarge : H ≤ delta
  · refine ⟨0, le_rfl, ?_⟩
    intro c hc hcurv x t ht htau
    exact False.elim (by dsimp only [H] at hlarge; linarith only [hlarge, htau, ht.2])
  have hsmall : delta < H := lt_of_not_ge hlarge
  obtain ⟨K0, hK0, hE0, hRm0, hRc0⟩ := m63Exists_firstJet_ambient_bounds F hcompact
  have hsmooth {d : ℕ} (t : ℝ) (Q : CovariantTensorEvaluation n M d)
      (hQ : IsSmoothCovariantTensor Q) (m : ℕ) :
      IsSmoothCovariantTensor ((F.connection t).iteratedCovariantTensorDerivative Q m) := by
    induction m with
    | zero => exact hQ
    | succ m ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t) ih
  obtain ⟨K1, hK1, hRm2⟩ := exists_uniform_tensor_bound F hcompact
    (fun t => (F.connection t).iteratedCovariantTensorDerivative
      (F.connection t).riemannEvaluation 2)
    (fun t => hsmooth t _ (M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t)) 2)
    (fun U hU X hX => M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F
      (fun t => M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t))
      (fun V hV Y hY => M04.contMDiffOn_flow_riemannEvaluation F hV Y hY) 2 hU hX)
  obtain ⟨K2, hK2, hRc3⟩ := exists_uniform_tensor_bound F hcompact
    (fun t => (F.connection t).iteratedCovariantTensorDerivative
      (F.connection t).ricciEvaluation 3)
    (fun t => hsmooth t _ (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t)) 3)
    (fun U hU X hX => M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F
      (fun t => M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))
      (fun V hV Y hY => M04.contMDiffOn_flow_ricciEvaluation F hV hY) 3 hU hX)
  let K := K0 + K1 + K2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hK0K : K0 ≤ K := by dsimp only [K]; linarith only [hK1, hK2]
  have hK1K : K1 ≤ K := by dsimp only [K]; linarith only [hK0, hK2]
  have hK2K : K2 ≤ K := by dsimp only [K]; linarith only [hK0, hK1]
  have hBounds : CurveEvolutionAmbientBounds F K K K := by
    refine ⟨?_, ?_, ?_⟩
    · intro s hs p v hv
      exact (hE0.riemann s hs p v hv).trans hK0K
    · intro s hs p v hv
      exact (hE0.ricci_derivative s hs p v hv).trans hK0K
    · intro s hs p v w hv hw
      exact (hE0.ricci s hs p v w hv hw).trans hK0K
  have hRiemann (s : ℝ) (hs : s ∈ Icc a b) (p : M)
      (v : Fin 5 → TangentSpace (𝓡 n) p) (hv : ∀ i, (F.metric s).tangentNorm p (v i) ≤ 1) :
      |(F.connection s).covariantTensorDerivative (F.connection s).riemannEvaluation p v| ≤ K :=
    (hRm0 s hs p v hv).trans hK0K
  have hSecond (s : ℝ) (hs : s ∈ Icc a b) (p : M)
      (v : Fin 4 → TangentSpace (𝓡 n) p) (hv : ∀ i, (F.metric s).tangentNorm p (v i) ≤ 1) :
      |(F.connection s).covariantTensorDerivative
        ((F.connection s).covariantTensorDerivative (F.connection s).ricciEvaluation) p v| ≤ K :=
    (hRc0 s hs p v hv).trans hK0K
  let A1 := 14 * R + 10 * K + 1
  let G1 := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
  let lambda := 1 + A1 * H
  let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
  let D1 := H * G1 + lambda * D0
  let B := 2 * lambda * R / delta + D1
  let P0 := K * (4 + 32 * (R + 1) + 27 * (B + 1) + 46 * R +
    33 * (R + 1) * (B + 1) + 10 * (R + 1) ^ 3) + 20 * (R + 1) * B
  let C1 := A1 + G1
  let C2 := 16 * K + 28 * R + 12 * (B + 1) + 1 + P0 ^ 2
  let Alpha := C1 + C2
  let Beta := D0 + C1 * H + C2 * H ^ 2
  let Cw := 3 + Alpha * H
  let Dw := Alpha * Cw ^ 2 * R + Beta * (Cw ^ 2 + Cw + 1)
  have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hG1 : 0 ≤ G1 := by dsimp only [G1]; positivity
  have hlambda : 0 ≤ lambda := by dsimp only [lambda]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD1 : 0 ≤ D1 := by dsimp only [D1]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC1 : 0 ≤ C1 := add_nonneg hA1 hG1
  have hC2 : 0 ≤ C2 := by dsimp only [C2]; positivity
  have hAlpha : 0 ≤ Alpha := add_nonneg hC1 hC2
  have hBeta : 0 ≤ Beta :=
    add_nonneg (add_nonneg hD0 (mul_nonneg hC1 hH)) (mul_nonneg hC2 (sq_nonneg H))
  have hCw : 0 ≤ Cw := add_nonneg (by norm_num) (mul_nonneg hAlpha hH)
  have hDw : 0 ≤ Dw :=
    add_nonneg (mul_nonneg (mul_nonneg hAlpha (sq_nonneg Cw)) hR)
      (mul_nonneg hBeta (add_nonneg (add_nonneg (sq_nonneg Cw) hCw) zero_le_one))
  refine ⟨4 * (Cw ^ 2 * R + Dw * H) / delta ^ 2, by positivity, ?_⟩
  intro c hc hcurv x t ht hage
  let tau := a + delta / 2
  have hatau : a < tau := by dsimp only [tau]; linarith only [hdelta]
  have htaub : tau < b := by
    dsimp only [tau]
    dsimp only [H] at hsmall
    linarith only [hsmall, hdelta]
  have hsub : Icc tau b ⊆ Icc a b := fun s hs => ⟨hatau.le.trans hs.1, hs.2⟩
  let F' := m63RestrictClosedFlow F tau b hsub htaub
  have hc' : M62ShrinkingCurve F' c :=
    m63SmoothRestriction (m63SmoothClosed_iff_m62.mpr hc) tau b hsub htaub
  have hjet (i : ℕ) (s y : ℝ) : m63CurvatureJet F' c i s y = m63CurvatureJet F c i s y := by
    induction i generalizing y with
    | zero => rfl
    | succ i ih =>
      change m62SpatialDerivative F c s (fun z => m63CurvatureJet F' c i s z) y =
        m62SpatialDerivative F c s (fun z => m63CurvatureJet F c i s z) y
      rw [show (fun z => m63CurvatureJet F' c i s z) =
        (fun z => m63CurvatureJet F c i s z) from funext ih]
  have hsq (i : ℕ) : m63CurvatureJetSquared F' c i = m63CurvatureJetSquared F c i := by
    funext s y
    simp only [m63CurvatureJetSquared, hjet]
    rfl
  have hinner (s : ℝ) (hs : s ∈ Ioo tau b) : s ∈ Ioo a b :=
    ⟨hatau.trans hs.1, hs.2⟩
  have hfirst (s : ℝ) (hs : s ∈ Ioo tau b) (y : ℝ) :
      m63CurvatureJetSquared F c 1 s y ≤ B := by
    have h := m63FirstJetSquared_short_time_bound F c hc hK hR hBounds
      hRiemann hSecond hcurv hH y s (hinner s hs) (sub_le_sub_right hs.2.le a)
    change m63CurvatureJetSquared F c 1 s y ≤ lambda * R / (s - a) + D1 at h
    have hden : delta / 2 ≤ s - a := by dsimp only [tau] at hs; linarith only [hs.1]
    have hratio : lambda * R / (s - a) ≤ 2 * lambda * R / delta := by
      calc
        _ ≤ lambda * R / (delta / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hlambda hR) (by positivity) hden
        _ = _ := by field_simp
    exact h.trans (add_le_add hratio le_rfl)
  have hqnon (i : ℕ) (s y : ℝ) : 0 ≤ m63CurvatureJetSquared F c i s y :=
    ((F.metric s).toRiemannianMetric.toCore (c y s)).re_inner_nonneg _
  have hzero (s : ℝ) (hs : s ∈ Ioo a b) (y : ℝ) :
      deriv (fun r => m63CurvatureJetSquared F c 0 r y) s -
          m62ArcSecondDerivative F c s (m63CurvatureJetSquared F c 0 s) y ≤
        -2 * m63CurvatureJetSquared F c 1 s y + D0 := by
    have hraw := spatial_squared_bound F c hc hK hK hK hBounds hs y
    have hsplit := spatialDerivative_norm_split F c hc hs y
    have hqR := hcurv s hs y
    change m62CurvatureSquared F c s y ≤ R at hqR
    have hkR : m62Curvature F c s y ≤ R + 1 := by
      nlinarith only [curvature_sq F c s y, hqR, sq_nonneg (m62Curvature F c s y - 1)]
    have hsum : m62CurvatureSquared F c s y + m62Curvature F c s y ≤ 2 * R + 1 := by
      linarith only [hqR, hkR]
    have hq2 : m62CurvatureSquared F c s y ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (curvatureSquared_nonneg F c s y) hqR 2
    change m63CurvatureJetSquared F c 1 s y =
      (F.metric s).inner (c y s) (m62SpatialNormalDerivative F c s y)
        (m62SpatialNormalDerivative F c s y) + m62CurvatureSquared F c s y ^ 2 at hsplit
    change deriv (fun r => m62CurvatureSquared F c r y) s -
      m62ArcSecondDerivative F c s (m62CurvatureSquared F c s) y ≤ _
    dsimp only [D0]
    nlinarith only [hraw, hsplit, hq2, mul_le_mul_of_nonneg_left hsum hC0]
  have hdiss : ∀ i ≤ 2, ∀ s ∈ Ioo tau b, s - tau ≤ H → ∀ y,
      deriv (fun r => m63CurvatureJetSquared F' c i r y) s -
          m62ArcSecondDerivative F' c s (m63CurvatureJetSquared F' c i s) y ≤
        -m63CurvatureJetSquared F' c (i + 1) s y +
          Alpha * m63CurvatureJetSquared F' c i s y + Beta / (s - tau) ^ i := by
    intro i hi s hs hsH y
    simp only [hsq]
    change deriv (fun r => m63CurvatureJetSquared F c i r y) s -
        m62ArcSecondDerivative F c s (m63CurvatureJetSquared F c i s) y ≤
      -m63CurvatureJetSquared F c (i + 1) s y +
        Alpha * m63CurvatureJetSquared F c i s y + Beta / (s - tau) ^ i
    have hst : 0 < s - tau := sub_pos.mpr hs.1
    interval_cases i
    · have h := hzero s (hinner s hs) y
      have hforcing : D0 ≤ Beta := by
        exact (le_add_of_nonneg_right (mul_nonneg hC1 hH)).trans
          (le_add_of_nonneg_right (mul_nonneg hC2 (sq_nonneg H)))
      simp only [pow_zero, div_one, Nat.zero_add]
      apply h.trans
      calc
        -2 * m63CurvatureJetSquared F c 1 s y + D0 ≤
            -m63CurvatureJetSquared F c 1 s y + Beta :=
          add_le_add (by linarith only [hqnon 1 s y]) hforcing
        _ ≤ _ := add_le_add
          (le_add_of_nonneg_right (mul_nonneg hAlpha (hqnon 0 s y))) le_rfl
    · have h := m63FirstJetSquared_dissipation F c hc hK hR hBounds (hinner s hs) y
        (hcurv s (hinner s hs) y)
        (hRiemann s (Ioo_subset_Icc_self (hinner s hs)) (c y s))
        (hSecond s (Ioo_subset_Icc_self (hinner s hs)) (c y s))
      have h' : deriv (fun r => m63CurvatureJetSquared F c 1 r y) s -
          m62ArcSecondDerivative F c s (m63CurvatureJetSquared F c 1 s) y ≤
        -m63CurvatureJetSquared F c 2 s y +
          C1 * m63CurvatureJetSquared F c 1 s y + C1 := by
        simpa only [C1, A1, G1, add_assoc] using h
      have hforcing : C1 ≤ Beta / (s - tau) := by
        apply (le_div_iff₀ hst).mpr
        exact (mul_le_mul_of_nonneg_left hsH hC1).trans
          ((le_add_of_nonneg_left hD0).trans
            (le_add_of_nonneg_right (mul_nonneg hC2 (sq_nonneg H))))
      simp only [pow_one]
      exact h'.trans (add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hC2) (hqnon 1 s y))) hforcing)
    · have h := m63SecondJetSquared_dissipation F c hc hK hR hB hBounds (hinner s hs) y
        (hcurv s (hinner s hs) y) (hfirst s hs y)
        (hRiemann s (Ioo_subset_Icc_self (hinner s hs)) (c y s))
        (fun v hv => (hRm2 s (Ioo_subset_Icc_self (hinner s hs)) (c y s) v hv).trans hK1K)
        (hSecond s (Ioo_subset_Icc_self (hinner s hs)) (c y s))
        (fun v hv => (hRc3 s (Ioo_subset_Icc_self (hinner s hs)) (c y s) v hv).trans hK2K)
      change _ ≤ -m63CurvatureJetSquared F c 3 s y +
        C2 * m63CurvatureJetSquared F c 2 s y + C2 at h
      have hforcing : C2 ≤ Beta / (s - tau) ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hst)).mpr
        exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hst.le hsH 2) hC2).trans
          (le_add_of_nonneg_left (add_nonneg hD0 (mul_nonneg hC1 hH)))
      exact h.trans (add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hC1) (hqnon 2 s y))) hforcing)
  have hfinite := m63CurvatureJetSquared_bound_of_finite_dissipation F' c hc' 2
    hAlpha hBeta hR hH (fun s hs _ y => by rw [hsq]; exact hcurv s (hinner s hs) y) hdiss
  have httau : tau < t := by dsimp only [tau]; linarith only [hage, hdelta]
  have hth : t - tau ≤ H := by dsimp only [tau, H]; linarith only [ht.2, hdelta]
  have hfin : m63CurvatureJetSquared F c 2 t x ≤
      (Cw ^ 2 * R + Dw * (t - tau)) / (t - tau) ^ 2 := by
    have h := hfinite x t ⟨httau, ht.2⟩ hth
    rw [hsq] at h
    convert h using 1
    norm_num [Cw, Dw, Finset.sum_range_succ]
  have hden : delta / 2 ≤ t - tau := by dsimp only [tau]; linarith only [hage]
  have hnum : 0 ≤ Cw ^ 2 * R + Dw * H := by positivity
  calc
    _ ≤ (Cw ^ 2 * R + Dw * (t - tau)) / (t - tau) ^ 2 := hfin
    _ ≤ (Cw ^ 2 * R + Dw * H) / (t - tau) ^ 2 :=
      div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hth hDw)) (sq_nonneg _)
    _ ≤ (Cw ^ 2 * R + Dw * H) / (delta / 2) ^ 2 :=
      div_le_div_of_nonneg_left hnum (by positivity)
        (pow_le_pow_left₀ (by positivity) hden 2)
    _ = _ := by
      rw [div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, div_div_eq_mul_div, mul_comm _ 4]

end PoincareConjecture
