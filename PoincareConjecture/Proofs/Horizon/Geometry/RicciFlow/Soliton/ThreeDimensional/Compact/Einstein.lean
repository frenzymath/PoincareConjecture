import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Differential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Constancy








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem mvfderiv_scalarCurvature_eq_zero_of_three_dimensional_einstein
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hEinstein : ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      D.ricci x v w = (D.scalarCurvature x / 3) * g.inner x v w)
    (x : M) (v : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) D.scalarCurvature x v = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have heq : D.ricciEvaluation =
      (fun y w => ((1 / 3 : ℝ) * D.scalarCurvature y) * g.inner y (w 0) (w 1)) := by
    funext y w
    simp only [ricciEvaluation, hEinstein]
    ring
  have ha : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun y => (1 / 3 : ℝ) * D.scalarCurvature y) :=
    contMDiff_const.mul D.contMDiff_scalarCurvature
  have hd (i) : mvfderiv (𝓡 3) D.scalarCurvature x (b i) = 0 := by
    have h := D.frameRicciDerivative_trace hD x i
    change (∑ p, D.covariantTensorDerivative D.ricciEvaluation x ![b p, b i, b p]) =
      mvfderiv (𝓡 3) D.scalarCurvature x (b i) / 2 at h
    simp_rw [heq, D.covariantTensorDerivative_scalar_mul_metric ha,
      PoincareConjecture.mvfderiv_const_mul] at h
    change (∑ p, (1 / 3 : ℝ) * mvfderiv (𝓡 3) D.scalarCurvature x (b p) *
      inner ℝ (b i) (b p)) = _ at h
    simp only [OrthonormalBasis.inner_eq_ite] at h
    simp at h
    linarith
  have hv := b.toBasis.sum_repr v
  rw [← hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_eq_zero fun i _ => by
    change _ * mvfderiv (𝓡 3) D.scalarCurvature x (b i) = 0
    rw [hd, mul_zero]


theorem constantPositiveSectionalCurvature_of_three_dimensional_einstein
    [PreconnectedSpace M] [Nonempty M]
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (hEinstein : ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      D.ricci x v w = (D.scalarCurvature x / 3) * g.inner x v w)
    (hR : ∀ x, 0 < D.scalarCurvature x) :
    ConstantPositiveSectionalCurvature g D := by
  obtain ⟨R, hconst⟩ := Poincare.Manifold.exists_eq_const_of_mvfderiv_eq_zero
    (fun x => (D.contMDiff_scalarCurvature x).mdifferentiableAt (by simp))
    (D.mvfderiv_scalarCurvature_eq_zero_of_three_dimensional_einstein hD hEinstein)
  have hpos : 0 < R := (hconst (Classical.arbitrary M)) ▸ hR (Classical.arbitrary M)
  refine ⟨R / 6, div_pos hpos (by norm_num), fun x v w hv hw hvw => ?_⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  have hvw' : inner ℝ v w = 0 := hvw
  have hwv : inner ℝ w v = 0 := by rw [real_inner_comm, hvw']
  have hframe : Orthonormal ℝ (({1, 2} : Set (Fin 3)).domRestrict ![0, v, w]) := by
    apply orthonormal_iff_ite.mpr
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = 1 ∨ i = 2 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
    have hj' : j = 1 ∨ j = 2 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · change inner ℝ v v = 1
      exact hv
    · simpa using hvw'
    · simpa using hwv
    · change inner ℝ w w = 1
      exact hw
  obtain ⟨b, hb⟩ := hframe.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (TangentSpace (𝓡 3) x) = Fintype.card (Fin 3) from
      finrank_euclideanSpace_fin)
  have hb1 : b 1 = v := by simpa using hb 1 (by simp)
  have hb2 : b 2 = w := by simpa using hb 2 (by simp)
  have h := D.ricciComplementTensor_apply_orthonormalBasis hD x b 0 0
  rw [D.ricciComplementTensor_apply] at h
  change (D.scalarCurvature x / 2) * inner ℝ (b 0) (b 0) -
    D.ricci x (b 0) (b 0) = _ at h
  rw [hEinstein] at h
  change (D.scalarCurvature x / 2) * inner ℝ (b 0) (b 0) -
    (D.scalarCurvature x / 3) * inner ℝ (b 0) (b 0) = _ at h
  simp only [b.inner_eq_ite, if_true] at h
  change D.scalarCurvature x / 2 * 1 - D.scalarCurvature x / 3 * 1 =
    D.curvatureTensor x (b 1) (b 2) (b 1) (b 2) at h
  rw [hb1, hb2, hconst] at h
  simp only [sectionalCurvature, hv, hw, hvw]
  norm_num
  linarith

end PoincareConjecture.LeviCivitaData
