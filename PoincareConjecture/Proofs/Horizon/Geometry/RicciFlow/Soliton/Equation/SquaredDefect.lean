import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def solitonDefectNormSq (D : LeviCivitaData g) (f : M → ℝ)
    (c : ℝ) (x : M) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, (D.ricci x (b i) (b j) + D.hessian f x (b i) (b j) -
    c * g.inner x (b i) (b j)) ^ 2

theorem solitonDefectNormSq_nonneg (D : LeviCivitaData g) (f : M → ℝ)
    (c : ℝ) (x : M) : 0 ≤ D.solitonDefectNormSq f c x :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem solitonDefectNormSq_eq_zero_iff (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (c : ℝ) (x : M) :
    D.solitonDefectNormSq f c x = 0 ↔
      ∀ u v : TangentSpace (𝓡 n) x,
        D.ricci x u v + D.hessian f x u v - c * g.inner x u v = 0 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let R := ∑ k, D.curvatureTensor_bilinear_first_third x (b k) (b k)
  have hR (u v : TangentSpace (𝓡 n) x) : R u v = D.ricci x u v := by
    simp only [R, LinearMap.sum_apply,
      curvatureTensor_bilinear_first_third_apply, ricci, b]
  have hH (u v : TangentSpace (𝓡 n) x) :
      D.hessian f x u v = g.inner x (D.connection (D.gradient f) x u) v :=
    D.hessian_eq_inner_connection_gradient (hf x) u v
  constructor
  · intro h u v
    have hentries (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
        D.ricci x (b i) (b j) + D.hessian f x (b i) (b j) -
          c * g.inner x (b i) (b j) = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg
          (D.ricci x (b i) (b j) + D.hessian f x (b i) (b j) -
            c * g.inner x (b i) (b j)))).mp h i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ sq_nonneg (D.ricci x (b i) (b j) + D.hessian f x (b i) (b j) -
          c * g.inner x (b i) (b j)))).mp hi j (Finset.mem_univ j))
    rw [← hR, hH, ← b.sum_repr u, ← b.sum_repr v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro j _
    have he := hentries j i
    rw [← hR, hH] at he
    linear_combination (b.repr v i * b.repr u j) * he
  · intro h
    simp only [solitonDefectNormSq, h, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero]

end PoincareConjecture.LeviCivitaData
