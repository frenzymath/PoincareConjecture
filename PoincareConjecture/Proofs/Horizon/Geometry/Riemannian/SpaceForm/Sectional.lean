import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Curvature







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem sectionalCurvature_eq_of_orthonormal (D : LeviCivitaData g)
    (x : M) (c : ℝ)
    (hc : ∀ a b : TangentSpace (𝓡 n) x,
      g.inner x a a = 1 → g.inner x b b = 1 → g.inner x a b = 0 →
        D.sectionalCurvature x a b = c)
    (u v : TangentSpace (𝓡 n) x)
    (hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0) :
    D.sectionalCurvature x u v = c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hu : u ≠ 0 := by
    rintro rfl
    simp at hgram
  have huu : 0 < g.inner x u u := real_inner_self_pos.mpr hu
  let μ := g.inner x u v / g.inner x u u
  let z := v - μ • u
  have huz : g.inner x u z = 0 := by
    change g.inner x u (v - μ • u) = 0
    rw [map_sub, map_smul]
    change g.inner x u v - μ * g.inner x u u = 0
    dsimp [μ]
    rw [div_mul_cancel₀ _ huu.ne', sub_self]
  have hgz : g.inner x u u * g.inner x z z =
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    dsimp [z]
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul,
      g.symm x v u]
    dsimp [μ]
    field_simp
    ring
  have hz : z ≠ 0 := by
    intro hz
    apply hgram
    rw [← hgz, hz]
    simp
  have hzz : 0 < g.inner x z z := real_inner_self_pos.mpr hz
  let a := (Real.sqrt (g.inner x u u))⁻¹
  let b := (Real.sqrt (g.inner x z z))⁻¹
  have ha : a * a * g.inner x u u = 1 := by
    dsimp [a]
    field_simp
    exact (Real.sq_sqrt huu.le).symm
  have hb : b * b * g.inner x z z = 1 := by
    dsimp [b]
    field_simp
    exact (Real.sq_sqrt hzz.le).symm
  have hpa : g.inner x (a • u) (a • u) = 1 := by
    simpa only [map_smul, smul_apply, smul_eq_mul, ← mul_assoc] using ha
  have hqb : g.inner x (b • z) (b • z) = 1 := by
    simpa only [map_smul, smul_apply, smul_eq_mul, ← mul_assoc] using hb
  have hpq : g.inner x (a • u) (b • z) = 0 := by
    simp only [map_smul, smul_apply, smul_eq_mul, huz, mul_zero]
  have hsec := hc (a • u) (b • z) hpa hqb hpq
  rw [sectionalCurvature, hpa, hqb, hpq] at hsec
  simp only [one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one,
    curvatureTensor_smul_first, curvatureTensor_smul_second,
    curvatureTensor_smul_third, curvatureTensor_smul_last] at hsec
  have hR : D.curvatureTensor x u z u z = D.curvatureTensor x u v u v := by
    dsimp [z]
    simp only [sub_eq_add_neg, ← neg_smul, curvatureTensor_add_second,
      curvatureTensor_add_last, curvatureTensor_smul_second,
      curvatureTensor_smul_last, curvatureTensor_zero_first,
      curvatureTensor_zero_last, mul_zero, add_zero]
  have hnum : D.curvatureTensor x u v u v =
      c * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
    rw [← hR, ← hgz]
    calc
      D.curvatureTensor x u z u z =
          (a * a * g.inner x u u) * (b * b * g.inner x z z) *
            D.curvatureTensor x u z u z := by rw [ha, hb]; ring
      _ = (b * (a * (b * (a * D.curvatureTensor x u z u z)))) *
          (g.inner x u u * g.inner x z z) := by ring
      _ = c * (g.inner x u u * g.inner x z z) := by rw [hsec]
  exact (div_eq_iff hgram).mpr hnum


theorem ricci_of_constant_sectional (D : LeviCivitaData g)
    (x : M) (c : ℝ)
    (hc : ∀ a b : TangentSpace (𝓡 n) x,
      g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 ≠ 0 →
        D.sectionalCurvature x a b = c)
    (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = ((n : ℝ) - 1) * c * g.inner x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsum := (g.orthonormalBasis x).sum_inner_mul_inner u v
  change (∑ i, g.inner x u (g.orthonormalBasis x i) *
    g.inner x (g.orthonormalBasis x i) v) = g.inner x u v at hsum
  have hunit (i) : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 := by
    change inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1
    simp
  unfold ricci
  simp_rw [D.curvatureTensor_of_constant_sectional x c hc, hunit, mul_one]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp_rw [mul_comm (g.inner x (g.orthonormalBasis x _) v)]
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    simp [TangentSpace]
  rw [hdim]
  ring


theorem scalarCurvature_of_constant_sectional (D : LeviCivitaData g)
    (x : M) (c : ℝ)
    (hc : ∀ a b : TangentSpace (𝓡 n) x,
      g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 ≠ 0 →
        D.sectionalCurvature x a b = c) :
    D.scalarCurvature x = (n : ℝ) * ((n : ℝ) - 1) * c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hunit (i) : g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 := by
    change inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1
    simp
  unfold scalarCurvature
  simp_rw [D.ricci_of_constant_sectional x c hc, hunit, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    simp [TangentSpace]
  rw [hdim]
  ring

end PoincareConjecture.LeviCivitaData
