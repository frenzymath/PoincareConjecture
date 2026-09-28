import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.AllOrderJetDissipation
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

theorem m63CurvatureJetSquared_bound_uniform_upper_cutoff [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (m : ℕ) {alpha B R delta : ℝ}
    (haalpha : a ≤ alpha) (halphaB : alpha < B) (hBb : B ≤ b)
    (hR : 0 ≤ R) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, alpha < s → s ≤ B →
      ∀ c : ℝ → ℝ → M, M63SmoothShrinkingCurveOn F c (Icc alpha s) →
        (∀ t ∈ Ioo alpha s, ∀ x, m63CurvatureJetSquared F c 0 t x ≤ R) →
        ∀ t ∈ Ioo alpha s, delta ≤ t - alpha → ∀ x,
          m63CurvatureJetSquared F c m t x ≤ C := by
  classical
  let H : ℝ := B - alpha
  have hH : 0 ≤ H := sub_nonneg.mpr halphaB.le
  obtain ⟨Kbase, hKbase, hEbase, hRmBase, hRcBase⟩ :=
    m63Exists_firstJet_ambient_bounds F hcompact
  have hsmooth {k : ℕ} (t : ℝ) (Q : CovariantTensorEvaluation n M k)
      (hQ : IsSmoothCovariantTensor Q) (d : ℕ) :
      IsSmoothCovariantTensor ((F.connection t).iteratedCovariantTensorDerivative Q d) := by
    induction d with
    | zero => exact hQ
    | succ d ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t) ih
  have hbound (d : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ p : M,
      (∀ v : Fin (4 + d) → TangentSpace (𝓡 n) p,
        (∀ i, (F.metric t).tangentNorm p (v i) ≤ 1) →
        |(F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).riemannEvaluation d p v| ≤ K) ∧
      (∀ v : Fin (2 + d) → TangentSpace (𝓡 n) p,
        (∀ i, (F.metric t).tangentNorm p (v i) ≤ 1) →
        |(F.connection t).iteratedCovariantTensorDerivative
          (F.connection t).ricciEvaluation d p v| ≤ K) := by
    obtain ⟨KR, hKR, hRm⟩ := exists_uniform_tensor_bound F hcompact
      (fun t => (F.connection t).iteratedCovariantTensorDerivative
        (F.connection t).riemannEvaluation d)
      (fun t => hsmooth t _ (M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t)) d)
      (fun U hU X hX => M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F
        (fun t => M04.isSmoothCovariantTensor_riemannEvaluation (F.connection t))
        (fun V hV Y hY => M04.contMDiffOn_flow_riemannEvaluation F hV Y hY) d hU hX)
    obtain ⟨KC, _hKC, hRc⟩ := exists_uniform_tensor_bound F hcompact
      (fun t => (F.connection t).iteratedCovariantTensorDerivative
        (F.connection t).ricciEvaluation d)
      (fun t => hsmooth t _ (M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t)) d)
      (fun U hU X hX => M04.contMDiffOn_flow_iteratedCovariantTensorDerivative F
        (fun t => M04.isSmoothCovariantTensor_ricciEvaluation (F.connection t))
        (fun V hV Y hY => M04.contMDiffOn_flow_ricciEvaluation F hV hY) d hU hX)
    refine ⟨max KR KC, hKR.trans (le_max_left _ _), ?_⟩
    intro t ht p
    exact ⟨fun v hv => (hRm t ht p v hv).trans (le_max_left _ _),
      fun v hv => (hRc t ht p v hv).trans (le_max_right _ _)⟩
  choose Kseq hKseq hTensor using hbound
  have hjet (l u : ℝ) (hsub : Icc l u ⊆ Icc a b) (hlu : l < u)
      (c : ℝ → ℝ → M) (i : ℕ) (t x : ℝ) :
      m63CurvatureJet (m63RestrictClosedFlow F l u hsub hlu) c i t x =
        m63CurvatureJet F c i t x := by
    induction i generalizing x with
    | zero => rfl
    | succ i ih =>
      change m62SpatialDerivative F c t
        (fun y => m63CurvatureJet (m63RestrictClosedFlow F l u hsub hlu) c i t y) x =
        m62SpatialDerivative F c t (fun y => m63CurvatureJet F c i t y) x
      rw [show (fun y => m63CurvatureJet (m63RestrictClosedFlow F l u hsub hlu) c i t y) =
        (fun y => m63CurvatureJet F c i t y) from funext ih]
  have hsq (l u : ℝ) (hsub : Icc l u ⊆ Icc a b) (hlu : l < u)
      (c : ℝ → ℝ → M) (i : ℕ) :
      m63CurvatureJetSquared (m63RestrictClosedFlow F l u hsub hlu) c i =
        m63CurvatureJetSquared F c i := by
    funext t x
    simp only [m63CurvatureJetSquared, hjet]
    rfl
  induction m using Nat.strong_induction_on generalizing delta with
  | h m ih =>
    by_cases hm0 : m = 0
    · subst m
      refine ⟨R, hR, ?_⟩
      intro s has hsB c hc hcurv t ht _hage x
      exact hcurv t ht x
    by_cases hlarge : H ≤ delta
    · refine ⟨0, le_rfl, ?_⟩
      intro s has hsB c hc hcurv t ht hage x
      exact False.elim (by dsimp only [H] at hlarge; linarith only [ht.2, hsB, hage, hlarge])
    by_cases hm1 : m = 1
    · subst m
      let A := 14 * R + 10 * Kbase + 1
      let G := 4 * R ^ 3 + 2 * R * Kbase * (7 * R + 6) +
        (Kbase * (46 * R + 32)) ^ 2
      let lam := 1 + A * H
      let D0 := 4 * R ^ 2 + m62C0 Kbase Kbase Kbase * (2 * R + 1)
      let D := H * G + lam * D0
      have hC0 : 0 ≤ m62C0 Kbase Kbase Kbase := by unfold m62C0; positivity
      have hA : 0 ≤ A := by dsimp only [A]; positivity
      have hG : 0 ≤ G := by dsimp only [G]; positivity
      have hlam : 0 ≤ lam := by dsimp only [lam]; positivity
      have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
      have hD : 0 ≤ D := by dsimp only [D]; positivity
      refine ⟨lam * R / delta + D, by positivity, ?_⟩
      intro s has hsB c hc hcurv t ht hage x
      have hsub : Icc alpha s ⊆ Icc a b := fun u hu =>
        ⟨haalpha.trans hu.1, hu.2.trans (hsB.trans hBb)⟩
      let Fs := m63RestrictClosedFlow F alpha s hsub has
      have hcs : M62ShrinkingCurve Fs c := m63SmoothRestriction hc alpha s Subset.rfl has
      have h := m63FirstJetSquared_short_time_bound Fs c hcs hKbase hR
        (m63RestrictAmbientBounds hEbase alpha s hsub has)
        (fun u hu p v hv => hRmBase u (hsub hu) p v hv)
        (fun u hu p v hv => hRcBase u (hsub hu) p v hv)
        (fun u hu y => hcurv u hu y) hH x t ht (by
          dsimp only [H]
          linarith only [ht.2, hsB])
      rw [hsq] at h
      change m63CurvatureJetSquared F c 1 t x ≤ lam * R / (t - alpha) + D at h
      exact h.trans (add_le_add
        (div_le_div_of_nonneg_left (mul_nonneg hlam hR) hdelta hage) le_rfl)
    have hI (i : Fin m) := ih i i.isLt (delta := delta / 2) (by positivity)
    choose Ci hCi hCiBound using hI
    let L := 1 + ∑ i : Fin m, Real.sqrt (Ci i)
    have hL : 1 ≤ L := le_add_of_nonneg_right
      (Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg (Ci i)))
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    let K := Kbase + ∑ d ∈ Finset.range (m + 2), Kseq d
    have hK : 0 ≤ K := add_nonneg hKbase (Finset.sum_nonneg (fun d _ => hKseq d))
    have hKbaseK : Kbase ≤ K := le_add_of_nonneg_right
      (Finset.sum_nonneg (fun d _ => hKseq d))
    have hKseqK (d : ℕ) (hd : d ≤ m + 1) : Kseq d ≤ K :=
      (Finset.single_le_sum (fun i _ => hKseq i)
        (Finset.mem_range.mpr (by omega : d < m + 2))).trans (le_add_of_nonneg_left hKbase)
    have hBounds : CurveEvolutionAmbientBounds F K K K := by
      refine ⟨?_, ?_, ?_⟩
      · intro u hu p v hv
        exact (hEbase.riemann u hu p v hv).trans hKbaseK
      · intro u hu p v hv
        exact (hEbase.ricci_derivative u hu p v hv).trans hKbaseK
      · intro u hu p v w hv hw
        exact (hEbase.ricci u hu p v w hv hw).trans hKbaseK
    let c0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
    let A1 := 14 * R + 10 * K + 1
    let G1 := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
    let c1 := A1 + G1
    let D0 : ℕ → ℝ := fun i => (Nat.factorial (i + 3) : ℝ) * K * L ^ (i + 3) +
      (2 : ℝ) ^ (i + 1) * L ^ 2
    let D1 : ℕ → ℝ := fun i => (2 : ℝ) ^ (i + 2) * D0 i * L +
      (m63JetErrorMassBound i : ℝ) * K * L ^ (i + 3)
    let T0 : ℕ → ℝ := fun i => (2 : ℝ) ^ (i + 1) * L ^ 3
    let coeff : ℕ → ℝ := fun i =>
      if i = 0 then c0 else if i = 1 then c1 else 2 * K + 4 * D1 i + T0 i ^ 2
    have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
    have hc0 : 0 ≤ c0 := by dsimp only [c0]; positivity
    have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
    have hG1 : 0 ≤ G1 := by dsimp only [G1]; positivity
    have hc1 : 0 ≤ c1 := add_nonneg hA1 hG1
    have hcoeff (i : ℕ) : 0 ≤ coeff i := by
      by_cases hi0 : i = 0
      · simpa only [coeff, if_pos hi0] using hc0
      by_cases hi1 : i = 1
      · simpa only [coeff, if_neg hi0, if_pos hi1] using hc1
      simp only [coeff, if_neg hi0, if_neg hi1]
      dsimp only [D0, D1, T0]
      positivity
    let Alpha : ℝ := ∑ i ∈ Finset.range (m + 1), coeff i
    let Beta : ℝ := ∑ i ∈ Finset.range (m + 1), coeff i * H ^ i
    let W : ℝ := (m : ℝ) + 1 + Alpha * H
    let D : ℝ := Alpha * W ^ m * R + Beta * ∑ i ∈ Finset.range (m + 1), W ^ (m - i)
    have hAlpha : 0 ≤ Alpha := Finset.sum_nonneg (fun i _ => hcoeff i)
    have hBeta : 0 ≤ Beta := Finset.sum_nonneg
      (fun i _ => mul_nonneg (hcoeff i) (pow_nonneg hH i))
    have hW : 0 ≤ W := by dsimp only [W]; positivity
    have hD : 0 ≤ D := add_nonneg
      (mul_nonneg (mul_nonneg hAlpha (pow_nonneg hW m)) hR)
      (mul_nonneg hBeta (Finset.sum_nonneg (fun i _ => pow_nonneg hW _)))
    refine ⟨(W ^ m * R + D * H) / (delta / 2) ^ m, by positivity, ?_⟩
    intro s has hsB c hc hcurv t ht hage x
    let tau := alpha + delta / 2
    have halphatau : alpha < tau := by dsimp only [tau]; linarith only [hdelta]
    have htaut : tau < t := by dsimp only [tau]; linarith only [hdelta, hage]
    have htaus : tau < s := htaut.trans ht.2
    have hsub : Icc tau s ⊆ Icc alpha s := fun u hu => ⟨halphatau.le.trans hu.1, hu.2⟩
    have hfull : Icc tau s ⊆ Icc a b := fun u hu =>
      ⟨haalpha.trans (hsub hu).1, hu.2.trans (hsB.trans hBb)⟩
    let F' := m63RestrictClosedFlow F tau s hfull htaus
    have hc' : M62ShrinkingCurve F' c := m63SmoothRestriction hc tau s hsub htaus
    have hinner (u : ℝ) (hu : u ∈ Ioo tau s) : u ∈ Ioo alpha s :=
      ⟨halphatau.trans hu.1, hu.2⟩
    have hcurv' (u : ℝ) (hu : u ∈ Ioo tau s) (y : ℝ) :
        m63CurvatureJetSquared F' c 0 u y ≤ R := hcurv u (hinner u hu) y
    have hLower (i : ℕ) (hi : i < m) (u : ℝ) (hu : u ∈ Ioo tau s) (y : ℝ) :
        (F'.metric u).tangentNorm (c y u) (m63CurvatureJet F' c i u y) ≤ L := by
      let ii : Fin m := ⟨i, hi⟩
      have hb := hCiBound ii s has hsB c hc hcurv u (hinner u hu) (by
        dsimp only [tau] at hu
        linarith only [hu.1]) y
      have hn := Real.sqrt_le_sqrt hb
      change (F.metric u).tangentNorm (c y u) (m63CurvatureJet F c i u y) ≤
        Real.sqrt (Ci ii) at hn
      change (F.metric u).tangentNorm (c y u)
        (m63CurvatureJet (m63RestrictClosedFlow F tau s hfull htaus) c i u y) ≤ L
      rw [hjet]
      exact hn.trans ((Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (Ci j))
        (Finset.mem_univ ii)).trans (le_add_of_nonneg_left zero_le_one))
    have hBounds' : CurveEvolutionAmbientBounds F' K K K :=
      m63RestrictAmbientBounds hBounds tau s hfull htaus
    have hqnon (i : ℕ) (u y : ℝ) : 0 ≤ m63CurvatureJetSquared F' c i u y :=
      ((F'.metric u).toRiemannianMetric.toCore (c y u)).re_inner_nonneg _
    have hzero (u : ℝ) (hu : u ∈ Ioo tau s) (y : ℝ) :
        deriv (fun r => m63CurvatureJetSquared F' c 0 r y) u -
            m62ArcSecondDerivative F' c u (m63CurvatureJetSquared F' c 0 u) y ≤
          -2 * m63CurvatureJetSquared F' c 1 u y + c0 := by
      have hraw := spatial_squared_bound F' c hc' hK hK hK hBounds' hu y
      have hsplit := spatialDerivative_norm_split F' c hc' hu y
      have hqR : m62CurvatureSquared F' c u y ≤ R := hcurv' u hu y
      have hkR : m62Curvature F' c u y ≤ R + 1 := by
        nlinarith only [curvature_sq F' c u y, hqR, sq_nonneg (m62Curvature F' c u y - 1)]
      have hsum : m62CurvatureSquared F' c u y + m62Curvature F' c u y ≤ 2 * R + 1 := by
        linarith only [hqR, hkR]
      have hq2 : m62CurvatureSquared F' c u y ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (curvatureSquared_nonneg F' c u y) hqR 2
      change m63CurvatureJetSquared F' c 1 u y =
        (F'.metric u).inner (c y u) (m62SpatialNormalDerivative F' c u y)
          (m62SpatialNormalDerivative F' c u y) + m62CurvatureSquared F' c u y ^ 2 at hsplit
      change deriv (fun r => m62CurvatureSquared F' c r y) u -
        m62ArcSecondDerivative F' c u (m62CurvatureSquared F' c u) y ≤ _
      dsimp only [c0]
      nlinarith only [hraw, hsplit, hq2, mul_le_mul_of_nonneg_left hsum hC0]
    have hpoint (i : ℕ) (hi : i ≤ m) (u : ℝ) (hu : u ∈ Ioo tau s) (y : ℝ) :
        deriv (fun r => m63CurvatureJetSquared F' c i r y) u -
            m62ArcSecondDerivative F' c u (m63CurvatureJetSquared F' c i u) y ≤
          -m63CurvatureJetSquared F' c (i + 1) u y +
            coeff i * m63CurvatureJetSquared F' c i u y + coeff i := by
      by_cases hi0 : i = 0
      · subst i
        simp only [coeff, if_pos rfl, Nat.zero_add]
        have h := hzero u hu y
        nlinarith only [h, hqnon 1 u y, mul_nonneg hc0 (hqnon 0 u y)]
      by_cases hi1 : i = 1
      · subst i
        have h := m63FirstJetSquared_dissipation F' c hc' hK hR hBounds' hu y
          (hcurv' u hu y)
          (fun v hv => (hRmBase u (hfull (Ioo_subset_Icc_self hu)) (c y u) v hv).trans hKbaseK)
          (fun v hv => (hRcBase u (hfull (Ioo_subset_Icc_self hu)) (c y u) v hv).trans hKbaseK)
        simpa only [coeff, if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl,
          if_true, Nat.reduceAdd, c1, A1, G1, add_assoc] using h
      have hi2 : 2 ≤ i := by omega
      have h := (m63CurvatureJetSquared_dissipation_of_lower_bounds F' c hc' i hi2 hK hL hu y
        (fun j hj => hLower j (lt_of_lt_of_le hj hi) u hu y)
        (fun d hd v hv =>
          ((hTensor d u (hfull (Ioo_subset_Icc_self hu)) (c y u)).1 v hv).trans
            (hKseqK d (by omega)))
        (fun d hd v hv =>
          ((hTensor d u (hfull (Ioo_subset_Icc_self hu)) (c y u)).2 v hv).trans
            (hKseqK d (by omega)))).2
      simpa only [coeff, if_neg hi0, if_neg hi1, D0, D1, T0] using h
    have hdiss : ∀ i ≤ m, ∀ u ∈ Ioo tau s, u - tau ≤ H → ∀ y,
        deriv (fun r => m63CurvatureJetSquared F' c i r y) u -
            m62ArcSecondDerivative F' c u (m63CurvatureJetSquared F' c i u) y ≤
          -m63CurvatureJetSquared F' c (i + 1) u y +
            Alpha * m63CurvatureJetSquared F' c i u y + Beta / (u - tau) ^ i := by
      intro i hi u hu huH y
      have hmem : i ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
      have hcoeffAlpha : coeff i ≤ Alpha := Finset.single_le_sum (fun j _ => hcoeff j) hmem
      have hcoeffBeta : coeff i * H ^ i ≤ Beta := Finset.single_le_sum
        (fun j _ => mul_nonneg (hcoeff j) (pow_nonneg hH j)) hmem
      have hagePos : 0 < u - tau := sub_pos.mpr hu.1
      have hforcing : coeff i ≤ Beta / (u - tau) ^ i := by
        apply (le_div_iff₀ (pow_pos hagePos i)).mpr
        exact (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hagePos.le huH i) (hcoeff i)).trans hcoeffBeta
      exact (hpoint i hi u hu y).trans (add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeffAlpha (hqnon i u y))) hforcing)
    have htH : t - tau ≤ H := by
      dsimp only [tau, H]
      linarith only [ht.2, hsB, hdelta]
    have hfinite : m63CurvatureJetSquared F' c m t x ≤
        (W ^ m * R + D * (t - tau)) / (t - tau) ^ m :=
      m63CurvatureJetSquared_bound_of_finite_dissipation F' c hc' m
        (A := Alpha) (B := Beta) (R := R) (H := H)
        hAlpha hBeta hR hH (fun u hu _ y => hcurv' u hu y) hdiss x t ⟨htaut, ht.2⟩ htH
    rw [hsq] at hfinite
    change m63CurvatureJetSquared F c m t x ≤
      (W ^ m * R + D * (t - tau)) / (t - tau) ^ m at hfinite
    have hden : delta / 2 ≤ t - tau := by dsimp only [tau]; linarith only [hage]
    have hnum : 0 ≤ W ^ m * R + D * H :=
      add_nonneg (mul_nonneg (pow_nonneg hW m) hR) (mul_nonneg hD hH)
    have hhalf : 0 < delta / 2 := half_pos hdelta
    calc
      _ ≤ (W ^ m * R + D * (t - tau)) / (t - tau) ^ m := hfinite
      _ ≤ (W ^ m * R + D * H) / (t - tau) ^ m := div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left htH hD))
        (pow_nonneg (sub_nonneg.mpr htaut.le) m)
      _ ≤ (W ^ m * R + D * H) / (delta / 2) ^ m :=
        div_le_div_of_nonneg_left hnum (pow_pos hhalf m)
          (pow_le_pow_left₀ hhalf.le hden m)

end PoincareConjecture
