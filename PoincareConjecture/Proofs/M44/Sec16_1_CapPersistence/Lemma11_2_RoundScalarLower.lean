import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundModelCurvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M44

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g h : RiemannianMetric 3 M}





theorem sectional_half_le_of_round_plane_error (D : LeviCivitaData h)
    (x : M) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 200)
    (hmetric : ∀ u v : TangentSpace (𝓡 3) x,
      |h.inner x u v - g.inner x u v| ≤
        epsilon * (g.tangentNorm x u * g.tangentNorm x v))
    (hcurv : ∀ u v : TangentSpace (𝓡 3) x,
      |D.curvatureTensor x u v u v -
        (g.inner x u u * g.inner x v v - g.inner x u v ^ 2)| ≤
          13 * epsilon * (g.inner x u u * g.inner x v v))
    (u v : TangentSpace (𝓡 3) x) (horth : LeviCivitaData.IsOrthonormalPair h x u v) :
    (1 / 2 : ℝ) ≤ D.sectionalCurvature x u v := by
  have hpos (z : TangentSpace (𝓡 3) x) : 0 ≤ g.inner x z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (g.pos x z hz).le
  have hsqrt (z : TangentSpace (𝓡 3) x) : g.tangentNorm x z ^ 2 = g.inner x z z :=
    Real.sq_sqrt (hpos z)
  have hquad (z : TangentSpace (𝓡 3) x) (hz : h.inner x z z = 1) :
      (4 / 5 : ℝ) ≤ g.inner x z z ∧ g.inner x z z ≤ 4 / 3 := by
    have he := hmetric z z
    rw [hz, ← sq, hsqrt] at he
    have habs := abs_le.mp he
    have heps : epsilon * g.inner x z z ≤ (1 / 4 : ℝ) * g.inner x z z :=
      mul_le_mul_of_nonneg_right (by linarith) (hpos z)
    constructor <;> linarith [habs.1, habs.2]
  obtain ⟨hu0, huv⟩ := hquad u horth.1
  obtain ⟨hv0, hvv⟩ := hquad v horth.2.1
  have hprod : g.inner x u u * g.inner x v v ≤ (16 / 9 : ℝ) := by
    nlinarith [mul_le_mul huv hvv (hpos v) (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have hprodlo : (16 / 25 : ℝ) ≤ g.inner x u u * g.inner x v v := by
    nlinarith [mul_le_mul hu0 hv0 (by norm_num : (0 : ℝ) ≤ 4 / 5) (hpos u)]
  have hnormprod : g.tangentNorm x u * g.tangentNorm x v ≤ (4 / 3 : ℝ) := by
    have hp : (g.tangentNorm x u * g.tangentNorm x v) ^ 2 =
        g.inner x u u * g.inner x v v := by rw [mul_pow, hsqrt, hsqrt]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (g.inner x u u))
      (Real.sqrt_nonneg (g.inner x v v))]
  have hcross : |g.inner x u v| ≤ (1 / 10 : ℝ) := by
    have he := hmetric u v
    rw [horth.2.2, zero_sub, abs_neg] at he
    have hb := mul_le_mul_of_nonneg_left hnormprod hepsilon
    linarith
  have hcrosssq : g.inner x u v ^ 2 ≤ (1 / 100 : ℝ) := by
    have hs := sq_le_sq₀ (abs_nonneg (g.inner x u v)) (by norm_num : (0 : ℝ) ≤ 1 / 10)
    have hh := hs.mpr hcross
    norm_num [sq_abs] at hh
    exact hh
  have herror : 13 * epsilon * (g.inner x u u * g.inner x v v) ≤ (26 / 225 : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hprod
      (show (0 : ℝ) ≤ 13 * epsilon from mul_nonneg (by norm_num) hepsilon)
    linarith
  have hlo := (abs_le.mp (hcurv u v)).1
  rw [LeviCivitaData.sectionalCurvature, horth.1, horth.2.1, horth.2.2]
  norm_num only [one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one]
  linarith




theorem scalarCurvature_three_le_of_sectional_half (D : LeviCivitaData h) (x : M)
    (hsec : ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair h x u v → (1 / 2 : ℝ) ≤ D.sectionalCurvature x u v) :
    3 ≤ D.scalarCurvature x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let b := h.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    unfold TangentSpace
    simp
  have hb (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      h.inner x (b i) (b j) = if i = j then 1 else 0 := b.inner_eq_ite i j
  have hc (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (if i = j then 0 else (1 / 2 : ℝ)) ≤ D.curvatureTensor x (b i) (b j) (b i) (b j) := by
    by_cases hij : i = j
    · subst j
      have hh := M04.curvatureTensor_swap_first D x (b i) (b i) (b i) (b i)
      simp only [ite_true]
      linarith
    · have horth : LeviCivitaData.IsOrthonormalPair h x (b i) (b j) := by
        simp only [LeviCivitaData.IsOrthonormalPair, hb, hij, ite_true, ite_false, and_self]
      have hs := hsec (b i) (b j) horth
      simpa only [LeviCivitaData.sectionalCurvature, hb, hij, ite_true, ite_false,
        one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using hs
  calc
    3 = ∑ i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          (if i = j then 0 else (1 / 2 : ℝ)) := by
      have he (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
          (if i = j then 0 else (1 / 2 : ℝ)) = 1 / 2 - (if i = j then 1 / 2 else 0) := by
        split_ifs <;> norm_num
      simp_rw [he, Finset.sum_sub_distrib]
      norm_num [hdim]
    _ ≤ ∑ i, ∑ j, D.curvatureTensor x (b i) (b j) (b i) (b j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hc i j
    _ = D.scalarCurvature x := rfl

end PoincareConjecture.M44
