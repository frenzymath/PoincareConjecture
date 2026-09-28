import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciContraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.PinchingAlgebra
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}



theorem exists_positive_ricci_spectrum (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 → 0 < D.ricci x v v) :
    ∃ a b c : ℝ, b ≤ a ∧ c ≤ b ∧ 0 < c ∧
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
  have hform (u v : TangentSpace (𝓡 3) x) : inner ℝ u (T v) = D.ricci x u v := by
    rw [D.ricci_eq_sum_frame x u v]
    conv_lhs => rw [← b.sum_repr' u, ← b.sum_repr' v]
    simp only [map_sum, map_smul, inner_sum, sum_inner,
      real_inner_smul_left, real_inner_smul_right, hentry]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change _ = C i j * inner ℝ (b i) u * inner ℝ (b j) v
    ring
  have hpos : 0 < e 2 := by
    have hp := hRic (v 2) (v.toBasis.ne_zero 2)
    rw [← hform, hT.apply_eigenvectorBasis hd] at hp
    simpa [v, e, real_inner_smul_right, (hT.eigenvectorBasis hd).inner_eq_ite] using hp
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
    hT.eigenvalues_antitone hd (by decide), hpos, ?_, ?_, ?_⟩
  · simpa only [pow_one, Matrix.trace, Matrix.diag_apply, C, b,
      Fin.sum_univ_three, scalarCurvature] using htrace 1
  · have h := htrace 2
    simp only [pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] at h
    simp_rw [hsym] at h
    simpa only [C, b, ← pow_two, Fin.sum_univ_three, ricciNormSq] using h
  · have h := htrace 3
    have hcubic : Matrix.trace (C ^ 3) = ∑ i, ∑ j, ∑ k, C i j * C j k * C k i := by
      rw [show C ^ 3 = C * C * C by noncomm_ring]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    rw [hcubic] at h
    simpa only [C, b, Fin.sum_univ_three] using h



theorem ricciNormSq_eq_scalarSq_div_three_of_reaction_nonneg
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 → 0 < D.ricci x v v)
    (hreact : 0 ≤ D.scalarCurvature x *
      (∑ i, ∑ j, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
        (∑ a, ∑ c, D.curvatureTensor x (g.orthonormalBasis x i) (g.orthonormalBasis x a)
          (g.orthonormalBasis x j) (g.orthonormalBasis x c) *
          D.ricci x (g.orthonormalBasis x a) (g.orthonormalBasis x c))) -
        D.ricciNormSq x ^ 2) :
    D.ricciNormSq x = D.scalarCurvature x ^ 2 / 3 := by
  obtain ⟨a, b, c, hab, hbc, hc, hR, hS, hcube⟩ :=
    D.exists_positive_ricci_spectrum hD x hRic
  rw [D.curvature_ricci_contraction_eq_cubic hD, hR, hS, hcube] at hreact
  have hP : Poincare.ThreeDimensionalRicciPinching.quartic a b c ≤ 0 := by
    rw [Poincare.ThreeDimensionalRicciPinching.quartic_eq_contracted_polynomial]
    dsimp only [Poincare.ThreeDimensionalRicciPinching.normSq,
      Poincare.ThreeDimensionalRicciPinching.scalar]
    nlinarith only [hreact]
  have hbound := Poincare.ThreeDimensionalRicciPinching.quartic_ge_least_sq_mul_traceFree
    hab hbc hc.le
  have hzero : Poincare.ThreeDimensionalRicciPinching.traceFreeNormSq a b c = 0 := by
    apply le_antisymm _ (Poincare.ThreeDimensionalRicciPinching.traceFreeNormSq_nonneg a b c)
    exact nonpos_of_mul_nonpos_right (hbound.trans hP)
      (mul_pos (by norm_num) (sq_pos_of_pos hc))
  dsimp only [Poincare.ThreeDimensionalRicciPinching.traceFreeNormSq,
    Poincare.ThreeDimensionalRicciPinching.normSq,
    Poincare.ThreeDimensionalRicciPinching.scalar] at hzero
  rw [hR, hS]
  linarith only [hzero]

theorem scalarCurvature_pos_of_ricci_pos (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 → 0 < D.ricci x v v) :
    0 < D.scalarCurvature x := by
  obtain ⟨a, b, c, hab, hbc, hc, hR, _, _⟩ := D.exists_positive_ricci_spectrum hD x hRic
  rw [hR]
  linarith

theorem scalarSq_div_three_le_ricciNormSq_of_ricci_pos
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 → 0 < D.ricci x v v) :
    D.scalarCurvature x ^ 2 / 3 ≤ D.ricciNormSq x := by
  obtain ⟨a, b, c, _, _, _, hR, hS, _⟩ := D.exists_positive_ricci_spectrum hD x hRic
  rw [hR, hS]
  exact sub_nonneg.mp (Poincare.ThreeDimensionalRicciPinching.traceFreeNormSq_nonneg a b c)



theorem ricci_eq_scalar_div_three_mul_inner_of_norm_eq
    (D : LeviCivitaData g) (x : M)
    (hnorm : D.ricciNormSq x = D.scalarCurvature x ^ 2 / 3)
    (u v : TangentSpace (𝓡 3) x) :
    D.ricci x u v = (D.scalarCurvature x / 3) * g.inner x u v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let C := fun i j => D.ricci x (b i) (b j)
  let R := D.scalarCurvature x
  have hd : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  have htrace : ∑ i, C i i = R := rfl
  have hsq : (∑ i, ∑ j, (C i j - if i = j then R / 3 else 0) ^ 2) = 0 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, hd, nsmul_eq_mul, htrace]
    change D.ricciNormSq x - 2 * R * (R / 3) + 3 * (R / 3) ^ 2 = 0
    rw [hnorm]
    dsimp only [R]
    ring
  have hC (i j) : C i j = if i = j then R / 3 else 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).mp hsq i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp
      hi j (Finset.mem_univ j)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hij)
  rw [D.ricci_eq_sum_frame]
  change (∑ i, ∑ j, C i j * inner ℝ (b i) u * inner ℝ (b j) v) = R / 3 * inner ℝ u v
  simp_rw [hC]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  have hs (i) : inner ℝ (b i) u = inner ℝ u (b i) := real_inner_comm _ _
  simp_rw [hs]
  exact b.sum_inner_mul_inner u v

end PoincareConjecture.LeviCivitaData
