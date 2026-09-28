import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Normal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Norm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.ScalarEvolution

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in
private theorem ricciNormSq_eq_sum_frame (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (b : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin 3) ℝ (TangentSpace (𝓡 3) x)) :
    D.ricciNormSq x = ∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hD.2.1.1 x
  have hs {ι : Type} [Fintype ι] (v : ι → TangentSpace (𝓡 3) x) :
      (∑ a : Fin 2 → ι, A (fun i => v (a i)) * A (fun i => v (a i))) =
        ∑ i, ∑ j, (D.ricci x (v i) (v j)) ^ 2 := by
    rw [Fintype.sum_equiv (finTwoArrowEquiv ι)
      (fun a => A (fun i => v (a i)) * A (fun i => v (a i)))
      (fun p => (D.ricci x (v p.1) (v p.2)) ^ 2) (fun a => ?_),
      Fintype.sum_prod_type]
    rw [← hA]
    rw [pow_two]
    rfl
  have he := multilinear_sum_mul_orthonormalBasis_eq A A (g.orthonormalBasis x) b
  rw [hs, hs] at he
  exact he

theorem ricciNormSq_eq_half_scalar_sq_of_null_direction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (N : TangentSpace (𝓡 3) x) (hN : g.inner x N N = 1)
    (hzero : ∀ u v w, D.curvatureTensor x N u v w = 0) :
    D.ricciNormSq x = (1 / 2 : ℝ) * D.scalarCurvature x ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  have hframe : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => N)) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have hij : i = j := Subtype.ext (i.2.trans j.2.symm)
    rw [if_pos hij]
    exact hN
  obtain ⟨b, hb⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have hb0 : b 0 = N := hb 0 (by simp)
  have z₁ (u v w) : D.curvatureTensor x (b 0) u v w = 0 := by rw [hb0]; exact hzero u v w
  have z₂ (u v w) : D.curvatureTensor x u (b 0) v w = 0 := by
    rw [D.curvatureTensor_swap_first, z₁, neg_zero]
  have z₃ (u v w) : D.curvatureTensor x u v (b 0) w = 0 := by
    rw [(hD.2.2.2.1 x u v (b 0) w).2.1, z₁]
  have d₁ (u v w) : D.curvatureTensor x u u v w = 0 := by
    linarith [D.curvatureTensor_swap_first x u u v w]
  have d₂ (u v w) : D.curvatureTensor x u v w w = 0 := by
    linarith [D.curvatureTensor_swap_last x u v w w]
  let K := D.curvatureTensor x (b 1) (b 2) (b 1) (b 2)
  have hswap : D.curvatureTensor x (b 2) (b 1) (b 2) (b 1) = K := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last x (b 1) (b 2), neg_neg]
  have hric (i j : Fin 3) : D.ricci x (b i) (b j) =
      if i = j ∧ i ≠ 0 then K else 0 := by
    rw [D.ricci_eq_sum_orthonormalBasis hD x b]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_succ, z₁, z₂, z₃, d₁, d₂, hswap, K]
  have hR : D.scalarCurvature x = 2 * K := by
    rw [D.scalarCurvature_eq_sum_orthonormalBasis x b]
    simp [Fin.sum_univ_succ, z₁, z₂, d₁, hswap, K]
    ring
  rw [D.ricciNormSq_eq_sum_frame hD x b, hR]
  simp [hric, Fin.sum_univ_succ]
  ring

theorem ricciNormSq_eq_half_scalar_sq_of_parallel_gradient
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hu : RiemannianMetric.HasUnitGradient D f)
    (hz : RiemannianMetric.HasZeroHessian D f) (x : M) :
    D.ricciNormSq x = (1 / 2 : ℝ) * D.scalarCurvature x ^ 2 := by
  exact D.ricciNormSq_eq_half_scalar_sq_of_null_direction hD x (D.gradient f x)
    (hu x) (RiemannianMetric.curvatureTensor_gradient_first_eq_zero hf hz x)

end PoincareConjecture.LeviCivitaData
