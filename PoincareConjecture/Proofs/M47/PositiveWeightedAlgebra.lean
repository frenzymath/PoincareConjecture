import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciSpectrum

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}

theorem exists_pinched_ricci_spectrum (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) {delta : ℝ}
    (hpinch : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
      delta * D.scalarCurvature x ≤ D.ricci x v v) :
    ∃ a b c : ℝ, b ≤ a ∧ c ≤ b ∧ delta * D.scalarCurvature x ≤ c ∧
      D.scalarCurvature x = a + b + c ∧ D.ricciNormSq x = a ^ 2 + b ^ 2 + c ^ 2 ∧
      (∑ i, ∑ j, ∑ k,
        D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
        D.ricci x (g.orthonormalBasis x j) (g.orthonormalBasis x k) *
        D.ricci x (g.orthonormalBasis x k) (g.orthonormalBasis x i)) =
          a ^ 3 + b ^ 3 + c ^ 3 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let C : Matrix _ _ ℝ := fun i j => D.ricci x (b i) (b j)
  let T : TangentSpace (𝓡 3) x →ₗ[ℝ] TangentSpace (𝓡 3) x :=
    C.toLin b.toBasis b.toBasis
  have hsym (i j) : C i j = C j i :=
    (hD.2.2.2.1 x (b i) (b j) (b i) (b j)).2.2.2
  have hT : T.IsSymmetric := (Matrix.isSymmetric_toLin_iff b).mpr (by
    ext i j
    exact hsym j i)
  have hd : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let e := hT.eigenvalues hd
  let v := hT.eigenvectorBasis hd
  have hentry (i j) : inner ℝ (b i) (T (b j)) = C i j := by
    have hm : LinearMap.toMatrix b.toBasis b.toBasis T = C :=
      LinearMap.toMatrix_toLin b.toBasis b.toBasis C
    simpa only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] using
      congrFun (congrFun hm i) j
  have hform (v w : TangentSpace (𝓡 3) x) : inner ℝ v (T w) = D.ricci x v w := by
    rw [D.ricci_eq_sum_frame x v w]
    conv_lhs => rw [← b.sum_repr' v, ← b.sum_repr' w]
    simp only [map_sum, map_smul, inner_sum, sum_inner,
      real_inner_smul_left, real_inner_smul_right, hentry]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change _ = C i j * inner ℝ (b i) v * inner ℝ (b j) w
    ring
  have hleast : delta * D.scalarCurvature x ≤ e 2 := by
    have hunit : g.inner x (v 2) (v 2) = 1 := by
      change inner ℝ (v 2) (v 2) = 1
      simp only [v, OrthonormalBasis.inner_eq_ite, if_true]
    have h := hpinch (v 2) hunit
    rw [← hform, hT.apply_eigenvectorBasis hd] at h
    simpa [v, e, real_inner_smul_right, OrthonormalBasis.inner_eq_ite] using h
  have htrace (k : ℕ) : Matrix.trace (C ^ k) = ∑ i, (e i) ^ k := by
    have hm : LinearMap.toMatrix b.toBasis b.toBasis T = C :=
      LinearMap.toMatrix_toLin b.toBasis b.toBasis C
    rw [← hm, LinearMap.toMatrix_pow,
      ← LinearMap.trace_eq_matrix_trace ℝ b.toBasis,
      LinearMap.trace_eq_matrix_trace ℝ v.toBasis,
      ← LinearMap.toMatrix_pow, hT.toMatrix_eigenvectorBasis hd,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  refine ⟨e 0, e 1, e 2, hT.eigenvalues_antitone hd (by decide),
    hT.eigenvalues_antitone hd (by decide), hleast, ?_, ?_, ?_⟩
  · simpa only [pow_one, Matrix.trace, Matrix.diag_apply, C, b,
      Fin.sum_univ_three, LeviCivitaData.scalarCurvature] using htrace 1
  · have h := htrace 2
    simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] at h
    simp_rw [hsym] at h
    simpa only [C, b, ← pow_two, Fin.sum_univ_three, LeviCivitaData.ricciNormSq] using h
  · have h := htrace 3
    have hcubic : Matrix.trace (C ^ 3) = ∑ i, ∑ j, ∑ k, C i j * C j k * C k i := by
      rw [show C ^ 3 = C * C * C by noncomm_ring]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    rw [hcubic] at h
    simpa only [C, b, Fin.sum_univ_three] using h

theorem weighted_ricci_reaction_nonpos (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) {delta epsilon : ℝ}
    (hdelta : 0 ≤ delta) (hR : 0 < D.scalarCurvature x)
    (hpinch : ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
      delta * D.scalarCurvature x ≤ D.ricci x v v)
    (hepsilon : epsilon ≤ 2 * delta ^ 2) :
    epsilon * D.ricciNormSq x * (D.ricciNormSq x - D.scalarCurvature x ^ 2 / 3) -
      (2 * D.ricciNormSq x ^ 2 - 2 * D.scalarCurvature x *
        (∑ i, ∑ j, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
          (∑ a, ∑ c, D.curvatureTensor x (g.orthonormalBasis x i)
            (g.orthonormalBasis x a) (g.orthonormalBasis x j) (g.orthonormalBasis x c) *
            D.ricci x (g.orthonormalBasis x a) (g.orthonormalBasis x c)))) ≤ 0 := by
  obtain ⟨a, b, c, hab, hbc, hleast, hscalar, hnorm, hcube⟩ :=
    exists_pinched_ricci_spectrum D hD x hpinch
  have hc : 0 ≤ c := (mul_nonneg hdelta hR.le).trans hleast
  have hp : delta * Poincare.ThreeDimensionalRicciPinching.scalar a b c ≤ c := by
    simpa only [Poincare.ThreeDimensionalRicciPinching.scalar, ← hscalar] using hleast
  have h := Poincare.ThreeDimensionalRicciPinching.weighted_reaction_numerator_nonpos
    hab hbc hc hdelta hp hepsilon
  rw [Poincare.ThreeDimensionalRicciPinching.quartic_eq_contracted_polynomial] at h
  rw [D.curvature_ricci_contraction_eq_cubic hD, hscalar, hnorm, hcube]
  exact h

theorem weighted_gradient_remainder_nonpos {R S A G p : ℝ}
    (hR : 0 < R) (hD : 0 ≤ S - R ^ 2 / 3) (hG : 0 ≤ G)
    (hp : 1 ≤ p) (hp' : p ≤ 2)
    (hK : (p * (S - R ^ 2 / 3) / R + 2 * R / 3) ^ 2 * G ≤ 4 * S * A) :
    -2 * A + (2 / 3 + p * (p - 1) * (S - R ^ 2 / 3) / R ^ 2) * G ≤ 0 := by
  have hS : 0 < S := by nlinarith [sq_pos_of_pos hR]
  have hid : (p * (S - R ^ 2 / 3) / R + 2 * R / 3) ^ 2 -
      2 * S * (2 / 3 + p * (p - 1) * (S - R ^ 2 / 3) / R ^ 2) =
      (2 - p) * (S - R ^ 2 / 3) *
        (p * (S - R ^ 2 / 3) / R ^ 2 + (2 / 3) * (p - 1)) := by
    field_simp [hR.ne']
    ring
  have hsign : 0 ≤ (2 - p) * (S - R ^ 2 / 3) *
      (p * (S - R ^ 2 / 3) / R ^ 2 + (2 / 3) * (p - 1)) := by
    have hp0 : 0 ≤ p := by linarith
    have hp1 : 0 ≤ p - 1 := by linarith
    have hp2 : 0 ≤ 2 - p := by linarith
    positivity
  have hbound := mul_le_mul_of_nonneg_right (sub_nonneg.mp (hid.symm ▸ hsign)) hG
  have hmul : (2 * S) *
      (-2 * A + (2 / 3 + p * (p - 1) * (S - R ^ 2 / 3) / R ^ 2) * G) ≤ 0 := by
    nlinarith only [hbound, hK]
  exact nonpos_of_mul_nonpos_right hmul (mul_pos (by norm_num) hS)

end PoincareConjecture.M47Positive
