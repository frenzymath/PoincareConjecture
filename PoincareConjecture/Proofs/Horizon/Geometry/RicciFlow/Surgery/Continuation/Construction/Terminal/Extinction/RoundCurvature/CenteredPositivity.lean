import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.CenteredBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology BigOperators InnerProductSpace

namespace PoincareConjecture.LeviCivitaData

open CoordinateExponential SingularRegularLimit.RoundComparison

variable {n : ℕ} {g h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem curvatureTensor_pos_orthonormal_of_centered_round_twoJet
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (x : EuclideanSpace ℝ (Fin n)) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon_small : epsilon ≤ 1 / 200)
    (hnormal : g.euclideanCoefficients x = innerSL ℝ)
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0)
    (hjet : ∀ j : ℕ, j ≤ 2 → ∀ v : Fin (2 + j) → EuclideanSpace ℝ (Fin n),
      |Dg.iteratedCovariantTensorDerivative (metricDifferenceTensor g h) j x v| ≤
        epsilon * ∏ i, ‖v i‖)
    (hround : ∀ a b : EuclideanSpace ℝ (Fin n),
      g.inner x a a = 1 → g.inner x b b = 1 → g.inner x a b = 0 →
        Dg.sectionalCurvature x a b = 1)
    (u v : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) :
    0 < Dh.curvatureTensor x u v u v := by
  let H := metricDifferenceTensor g h
  let q := 3 * epsilon / (2 * (1 - epsilon))
  have heone : epsilon < 1 := by linarith
  have hmetric (w : EuclideanSpace ℝ (Fin n)) : |H x ![w, w]| ≤ epsilon * ‖w‖ ^ 2 := by
    have hj := hjet 0 (by omega) ![w, w]
    simpa [iteratedCovariantTensorDerivative, Fin.prod_univ_succ, pow_two, mul_assoc, H] using hj
  have hfirst (a b c : EuclideanSpace ℝ (Fin n)) :
      |Dg.covariantTensorDerivative H x ![a, b, c]| ≤ epsilon * ‖a‖ * ‖b‖ * ‖c‖ := by
    have hj := hjet 1 (by omega) ![a, b, c]
    simpa [iteratedCovariantTensorDerivative, Fin.prod_univ_succ, mul_assoc, H] using hj
  have hsecond (a b c d : EuclideanSpace ℝ (Fin n)) :
      |Dg.covariantTensorDerivative (Dg.covariantTensorDerivative H) x ![a, b, c, d]| ≤
        epsilon * ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
    have hj := hjet 2 (by omega) ![a, b, c, d]
    simpa [iteratedCovariantTensorDerivative, Fin.prod_univ_succ, mul_assoc, H] using hj
  have hnormΓ (a b : EuclideanSpace ℝ (Fin n)) :
      ‖Dh.euclideanConnection a b x‖ ≤ q * ‖a‖ * ‖b‖ :=
    Dg.norm_euclideanConnection_le_of_covariantMetricDifference Dh x hepsilon heone
      hnormal hzero hmetric hfirst a b
  have hpair (a b c d : EuclideanSpace ℝ (Fin n)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
      |h.inner x (Dh.euclideanConnection a b x) (Dh.euclideanConnection c d x)| ≤
        (3 / 2 : ℝ) * epsilon * q := by
    have hp := Dg.abs_euclideanConnection_pairing_le_of_covariantMetricDifference Dh x
      hzero hfirst a b (Dh.euclideanConnection c d x)
    have hn := hnormΓ c d
    simp only [ha, hb, hc, hd, mul_one] at hp hn
    exact hp.trans (mul_le_mul_of_nonneg_left hn (by positivity))
  have hquad₁ := abs_le.mp (hpair u v v u hu hv hv hu)
  have hquad₂ := abs_le.mp (hpair v v u u hv hv hu hu)
  have hcoeff (a b : EuclideanSpace ℝ (Fin n)) : g.inner x a b = inner ℝ a b := by
    change g.euclideanCoefficients x a b = _
    rw [hnormal]
    rfl
  have hguu : g.inner x u u = 1 := by rw [hcoeff, real_inner_self_eq_norm_sq, hu]; norm_num
  have hgvv : g.inner x v v = 1 := by rw [hcoeff, real_inner_self_eq_norm_sq, hv]; norm_num
  have hguv : g.inner x u v = 0 := by rw [hcoeff, huv]
  have hgvu : g.inner x v u = 0 := by rw [g.symm, hguv]
  have hsec := Dg.sectionalCurvature_eq_of_orthonormal x 1 hround
  have hRv : Dg.curvature x u v v = u := by
    apply (g.inner_isInvertible x).injective
    ext w
    change Dg.curvatureTensor x u v w v = g.inner x u w
    rw [Dg.curvatureTensor_of_constant_sectional x 1 hsec]
    simp only [hgvv, hguv, mul_one, mul_zero, sub_zero, one_mul]
  have hRu : Dg.curvature x u v u = -v := by
    apply (g.inner_isInvertible x).injective
    ext w
    change Dg.curvatureTensor x u v w u = g.inner x (-v) w
    rw [Dg.curvatureTensor_of_constant_sectional x 1 hsec]
    simp only [hgvu, hguu, mul_zero, mul_one, zero_sub, one_mul, map_neg, neg_apply]
  have hR : Dg.curvatureTensor x u v u v = 1 := by
    have hs := hround u v hguu hgvv hguv
    simpa [sectionalCurvature, hguu, hgvv, hguv] using hs
  have hH₁ := abs_le.mp (hmetric u)
  have hH₂ : -epsilon ≤ H x ![-v, v] ∧ H x ![-v, v] ≤ epsilon := by
    simpa [iteratedCovariantTensorDerivative, Fin.prod_univ_succ, H, hv] using
      abs_le.mp (hjet 0 (by omega) ![-v, v])
  have hS₁ := abs_le.mp (hsecond u v v u)
  have hS₂ := abs_le.mp (hsecond u u v v)
  have hS₃ := abs_le.mp (hsecond v v u u)
  have hS₄ := abs_le.mp (hsecond v u u v)
  simp only [hu, hv, one_pow, mul_one] at hH₁ hS₁ hS₂ hS₃ hS₄
  have hformula := Dg.curvatureTensor_sub_eq_covariant_metricDifference Dh x u v u v hzero
  dsimp only at hformula
  rw [hRv, hRu, hR] at hformula
  have hq : q ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * (1 - epsilon))).mpr
    linarith
  have hεq : epsilon * q ≤ epsilon := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq hepsilon
  nlinarith only [hepsilon_small, hεq, hformula, hH₁.1, hH₂.2,
    hS₁.1, hS₂.2, hS₃.2, hS₄.1, hquad₁.1, hquad₂.2]

theorem curvatureTensor_pos_of_euclidean_orthonormal
    (D : LeviCivitaData h) (x : EuclideanSpace ℝ (Fin n))
    (hpos : ∀ u v : EuclideanSpace ℝ (Fin n),
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 → 0 < D.curvatureTensor x u v u v)
    (u v : EuclideanSpace ℝ (Fin n)) (hlin : LinearIndependent ℝ ![u, v]) :
    0 < D.curvatureTensor x u v u v := by
  obtain ⟨a, b, c, d, hdet, hp, hq, hpq⟩ := exists_orthonormal_changeBasis u v hlin
  have hpn : ‖a • u + b • v‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hp
    nlinarith [norm_nonneg (a • u + b • v)]
  have hqn : ‖c • u + d • v‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hq
    nlinarith [norm_nonneg (c • u + d • v)]
  have hnum : D.curvatureTensor x (a • u + b • v) (c • u + d • v)
      (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
    let u' : TangentSpace (𝓡 n) x := u
    let v' : TangentSpace (𝓡 n) x := v
    change D.curvatureTensor x (a • u' + b • v') (c • u' + d • v')
      (a • u' + b • v') (c • u' + d • v') =
      (a * d - b * c) ^ 2 * D.curvatureTensor x u' v' u' v'
    simp only [curvatureTensor_add_first, curvatureTensor_add_second,
      curvatureTensor_add_third, curvatureTensor_add_last,
      curvatureTensor_smul_first, curvatureTensor_smul_second,
      curvatureTensor_smul_third, curvatureTensor_smul_last,
      curvatureTensor_zero_first, curvatureTensor_zero_last]
    rw [curvatureTensor_swap_first, curvatureTensor_swap_last,
      D.curvatureTensor_swap_first x v' u' u' v']
    ring
  have hh := hpos (a • u + b • v) (c • u + d • v) hpn hqn hpq
  rw [hnum] at hh
  exact pos_of_mul_pos_right hh (sq_nonneg _)

theorem curvatureTensor_pos_of_centered_round_twoJet
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    (x : EuclideanSpace ℝ (Fin n)) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon_small : epsilon ≤ 1 / 200)
    (hnormal : g.euclideanCoefficients x = innerSL ℝ)
    (hzero : christoffelBilinear g.euclideanCoefficients x = 0)
    (hjet : ∀ j : ℕ, j ≤ 2 → ∀ v : Fin (2 + j) → EuclideanSpace ℝ (Fin n),
      |Dg.iteratedCovariantTensorDerivative (metricDifferenceTensor g h) j x v| ≤
        epsilon * ∏ i, ‖v i‖)
    (hround : ∀ a b : EuclideanSpace ℝ (Fin n),
      g.inner x a a = 1 → g.inner x b b = 1 → g.inner x a b = 0 →
        Dg.sectionalCurvature x a b = 1)
    (u v : EuclideanSpace ℝ (Fin n)) (hlin : LinearIndependent ℝ ![u, v]) :
    0 < Dh.curvatureTensor x u v u v :=
  Dh.curvatureTensor_pos_of_euclidean_orthonormal x
    (Dg.curvatureTensor_pos_orthonormal_of_centered_round_twoJet Dh x
      hepsilon hepsilon_small hnormal hzero hjet hround) u v hlin

end PoincareConjecture.LeviCivitaData
