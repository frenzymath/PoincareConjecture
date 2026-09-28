import PoincareConjecture.Proofs.M35.CapGeometry.RoundSurfaceParallel
import PoincareConjecture.Proofs.M13.CurvatureContractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

local notation "E2" => EuclideanSpace ℝ (Fin 2)

theorem surface_ricci_of_sectional
    {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M]
    [IsManifold (𝓡 2) ∞ M] [T2Space M]
    {g : RiemannianMetric 2 M} (D : LeviCivitaData g) (x : M) (c : ℝ)
    (hsection : ∀ u v : TangentSpace (𝓡 2) x,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
        D.sectionalCurvature x u v = c)
    (u v : TangentSpace (𝓡 2) x) : D.ricci x u v = c * g.inner x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := finrank_euclideanSpace_fin
  let b := (g.orthonormalBasis x).reindex (finCongr hdim)
  have hinner (i j : Fin 2) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have h00 : g.inner x (b 0) (b 0) = 1 := by simp only [hinner, ite_true]
  have h11 : g.inner x (b 1) (b 1) = 1 := by simp only [hinner, ite_true]
  have h01 : g.inner x (b 0) (b 1) = 0 := by simp only [hinner, Fin.zero_ne_one, ite_false]
  have hK : D.curvatureTensor x (b 0) (b 1) (b 0) (b 1) = c := by
    have h := hsection (b 0) (b 1) h00 h11 h01
    simpa only [LeviCivitaData.sectionalCurvature, h00, h11, h01,
      mul_one, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_one] using h
  have hpair : D.curvatureTensor x (b 1) (b 0) (b 1) (b 0) = c := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last, neg_neg]
    exact hK
  have hricci (i j : Fin 2) : D.ricci x (b i) (b j) = c * g.inner x (b i) (b j) := by
    rw [M13.ricci_eq_sum_basis D x b, Fin.sum_univ_two, hinner]
    fin_cases i <;> fin_cases j <;>
      simp [D.curvatureTensor_zero_first, D.curvatureTensor_zero_last, hK, hpair]
  have hu : (b.repr u) 0 • b 0 + (b.repr u) 1 • b 1 = u := by
    simpa only [Fin.sum_univ_two] using b.sum_repr u
  have hv : (b.repr v) 0 • b 0 + (b.repr v) 1 • b 1 = v := by
    simpa only [Fin.sum_univ_two] using b.sum_repr v
  rw [← hu, ← hv]
  change M13.ricciLinear D x _ _ = _
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    add_apply, smul_apply, smul_eq_mul, M13.ricciLinear_apply, hricci]
  ring

theorem surface_scalar_of_sectional
    {M : Type*} [TopologicalSpace M] [ChartedSpace E2 M]
    [IsManifold (𝓡 2) ∞ M] [T2Space M]
    {g : RiemannianMetric 2 M} (D : LeviCivitaData g) (x : M) (c : ℝ)
    (hsection : ∀ u v : TangentSpace (𝓡 2) x,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
        D.sectionalCurvature x u v = c) : D.scalarCurvature x = 2 * c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := finrank_euclideanSpace_fin
  let b := (g.orthonormalBasis x).reindex (finCongr hdim)
  rw [M13.scalarCurvature_eq_sum_basis D x b, Fin.sum_univ_two,
    surface_ricci_of_sectional D x c hsection, surface_ricci_of_sectional D x c hsection]
  have hinner (i : Fin 2) : g.inner x (b i) (b i) = 1 := by
    have h : g.inner x (b i) (b i) = if i = i then 1 else 0 := b.inner_eq_ite i i
    simpa only [ite_true] using h
  rw [hinner, hinner]
  ring

end PoincareConjecture.M35
