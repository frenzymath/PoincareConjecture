import PoincareConjecture.Proofs.M47.PositiveGradientQuotient

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47Positive

section GeneralDimension

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem scalar_ricci_gradient_pairing_le (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hR : 0 < D.scalarCurvature x)
    (hS : D.ricciNormSq x ≤ D.scalarCurvature x ^ 2) :
    g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.ricciNormSq x) ≤
      D.scalarCurvature x *
        ((∑ k, ∑ i, ∑ j, (D.covariantTensorDerivative D.ricciEvaluation x
          ![g.orthonormalBasis x k, g.orthonormalBasis x i, g.orthonormalBasis x j]) ^ 2) +
          g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x)) := by
  let R := D.scalarCurvature x
  let S := D.ricciNormSq x
  let A := ∑ k, ∑ i, ∑ j, (D.covariantTensorDerivative D.ricciEvaluation x
    ![g.orthonormalBasis x k, g.orthonormalBasis x i, g.orthonormalBasis x j]) ^ 2
  let v := D.gradient D.scalarCurvature x
  let w := D.gradient D.ricciNormSq x
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpair : g.tensorPairingTwo D.ricciEvaluation D.ricciEvaluation = D.ricciNormSq := by
    funext y
    simp only [RiemannianMetric.tensorPairingTwo, LeviCivitaData.ricciNormSq,
      LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one, pow_two]
  have hK := D.gradient_tensor_normSq_le hD.2.1 x
  dsimp only at hK
  rw [hpair] at hK
  have hK' : g.inner x w w ≤ 4 * S * A := by
    simpa only [RiemannianMetric.tensorPairingThree, ← pow_two] using hK
  have hSA := mul_le_mul_of_nonneg_right hS hA
  have hsq : 0 ≤ g.inner x (w - (2 * R) • v) (w - (2 * R) • v) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change 0 ≤ inner ℝ (w - (2 * R) • v) (w - (2 * R) • v)
    exact real_inner_self_nonneg
  have hid : g.inner x (w - (2 * R) • v) (w - (2 * R) • v) =
      g.inner x w w - 4 * R * g.inner x v w + 4 * R ^ 2 * g.inner x v v := by
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
    rw [g.symm x w v]
    ring
  rw [hid] at hsq
  have hmul : (4 * R) * (g.inner x v w - R * (A + g.inner x v v)) ≤ 0 := by
    change S * A ≤ R ^ 2 * A at hSA
    nlinarith only [hK', hSA, hsq]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hmul (mul_pos (by norm_num) hR))

end GeneralDimension

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}

theorem ricci_norm_bounds_of_nonneg (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 → 0 ≤ D.ricci x v v) :
    D.scalarCurvature x ^ 2 / 3 ≤ D.ricciNormSq x ∧
      D.ricciNormSq x ≤ D.scalarCurvature x ^ 2 := by
  obtain ⟨a, b, c, hab, hbc, hc, hscalar, hnorm, _⟩ :=
    exists_pinched_ricci_spectrum D hD x (delta := 0) (by simpa using hRic)
  have hc0 : 0 ≤ c := by simpa using hc
  have hb0 : 0 ≤ b := hc0.trans hbc
  have ha0 : 0 ≤ a := hb0.trans hab
  rw [hscalar, hnorm]
  constructor
  · exact sub_nonneg.mp (Poincare.ThreeDimensionalRicciPinching.traceFreeNormSq_nonneg a b c)
  · nlinarith only [mul_nonneg ha0 hb0, mul_nonneg ha0 hc0, mul_nonneg hb0 hc0]

theorem ricci_defect_reaction_le (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) (hR : 0 < D.scalarCurvature x)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 → 0 ≤ D.ricci x v v) :
    4 * (∑ i, ∑ j, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
      (∑ a, ∑ c, D.curvatureTensor x (g.orthonormalBasis x i)
        (g.orthonormalBasis x a) (g.orthonormalBasis x j) (g.orthonormalBasis x c) *
        D.ricci x (g.orthonormalBasis x a) (g.orthonormalBasis x c))) -
      (4 / 3) * D.scalarCurvature x * D.ricciNormSq x ≤
        4 * D.scalarCurvature x * (D.ricciNormSq x - D.scalarCurvature x ^ 2 / 3) := by
  have hnorm := ricci_norm_bounds_of_nonneg D hD x hRic
  have hP := weighted_ricci_reaction_nonpos D hD x (delta := 0) (epsilon := 0)
    (by norm_num) hR (by simpa using hRic) (by norm_num)
  simp only [zero_mul, zero_sub, neg_nonpos] at hP
  have hprod := mul_le_mul_of_nonneg_right hnorm.2 (sub_nonneg.mpr hnorm.1)
  apply (mul_le_mul_iff_right₀ hR).mp
  nlinarith only [hP, hprod]

end PoincareConjecture.M47Positive
