import PoincareConjecture.Proofs.M13.CurvatureMultilinear
import PoincareConjecture.Proofs.M13.BasisContractions

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {g : RiemannianMetric n M}

noncomputable def ricciLinear (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (D.ricci x)
    (fun u u' v ↦ by
      simp only [LeviCivitaData.ricci, ← curvatureTensorLinear_apply, map_add,
        LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c u v ↦ by
      simp only [LeviCivitaData.ricci, ← curvatureTensorLinear_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum])
    (fun u v v' ↦ by
      simp only [LeviCivitaData.ricci, ← curvatureTensorLinear_apply, map_add,
        LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c u v ↦ by
      simp only [LeviCivitaData.ricci, ← curvatureTensorLinear_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum])

theorem ricciLinear_apply (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ricciLinear D x u v = D.ricci x u v := rfl

theorem ricci_eq_sum_basis (D : LeviCivitaData g) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x))
      (u v : TangentSpace (𝓡 n) x),
      D.ricci x u v = ∑ i, D.curvatureTensor x u (b i) v (b i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  intro ι _ b u v
  exact sum_bilinear_diagonal_basis_eq ((curvatureTensorLinear D x u).flip v)
    (g.orthonormalBasis x) b

theorem scalarCurvature_eq_sum_basis (D : LeviCivitaData g) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x)),
      D.scalarCurvature x = ∑ i, D.ricci x (b i) (b i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  intro ι _ b
  exact sum_bilinear_diagonal_basis_eq (ricciLinear D x) (g.orthonormalBasis x) b

theorem curvatureTensorNorm_eq_sqrt_sum_basis (D : LeviCivitaData g) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x)),
      D.curvatureTensorNorm x = Real.sqrt
        (∑ i, ∑ j, ∑ k, ∑ l, (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  intro ι _ b
  exact congrArg Real.sqrt (sum_sq_fourlinear_basis_eq
    (curvatureTensorLinear D x) (g.orthonormalBasis x) b)

end PoincareConjecture.M13
