import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.Matrix
import Mathlib.Analysis.Matrix.Normed

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter
open scoped Topology Matrix.Norms.Elementwise

namespace PoincareConjecture.RiemannianMetric

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def transverseOperator (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (Matrix.toEuclideanLin ((LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix
    Fin.succ Fin.succ)).toContinuousLinearMap

@[simp] theorem toMatrix_transverseOperator
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis (transverseOperator b A).toLinearMap =
      (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap).submatrix Fin.succ Fin.succ := by
  simp [transverseOperator, Matrix.toEuclideanLin_eq_toLin_orthonormal]

theorem transverseOperator_comp
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A B : E →L[ℝ] E)
    (hrad : A (b 0) = 0) :
    transverseOperator b (A.comp B) = (transverseOperator b A).comp (transverseOperator b B) := by
  apply ContinuousLinearMap.coe_injective
  apply (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis).injective
  simp only [ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis,
    toMatrix_transverseOperator]
  rw [LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ]
  simp [LinearMap.toMatrix_apply, hrad]

@[simp] theorem transverseOperator_zero
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) : transverseOperator b 0 = 0 := by
  simp [transverseOperator, Matrix.submatrix_zero]

@[simp] theorem transverseOperator_neg
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E) :
    transverseOperator b (-A) = -transverseOperator b A := by
  simp [transverseOperator, Matrix.submatrix_neg]

theorem hasDerivAt_transverseOperator
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E)
    {A : ℝ → E →L[ℝ] E} {A' : E →L[ℝ] E} {t : ℝ} (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => transverseOperator b (A s)) (transverseOperator b A') t := by
  let C : Matrix (Fin m) (Fin m) ℝ ≃L[ℝ]
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  have hd : HasDerivAt
      (fun s => (LinearMap.toMatrix b.toBasis b.toBasis (A s).toLinearMap).submatrix
        Fin.succ Fin.succ)
      ((LinearMap.toMatrix b.toBasis b.toBasis A'.toLinearMap).submatrix Fin.succ Fin.succ) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j =>
      hasDerivAt_toMatrix_operator b hA i.succ j.succ
  exact C.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd

theorem isSymmetric_transverseOperator
    (b : OrthonormalBasis (Fin (m + 1)) ℝ E) (A : E →L[ℝ] E)
    (hA : LinearMap.IsSymmetric A.toLinearMap) :
    LinearMap.IsSymmetric (transverseOperator b A).toLinearMap := by
  apply (LinearMap.isHermitian_toMatrix_iff (EuclideanSpace.basisFun (Fin m) ℝ)).mp
  rw [toMatrix_transverseOperator, Matrix.isHermitian_iff_isSymm]
  exact isSymm_transverse b A hA

theorem isInvertible_of_toMatrix_det_ne_zero
    {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (b : Module.Basis ι ℝ F) (A : F →L[ℝ] F)
    (hA : (LinearMap.toMatrix b b A.toLinearMap).det ≠ 0) : A.IsInvertible := by
  let B := LinearMap.toMatrix b b A.toLinearMap
  let e := Matrix.toLinOfInv b b (Matrix.mul_nonsing_inv B hA.isUnit)
    (Matrix.nonsing_inv_mul B hA.isUnit)
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.coe_injective
  exact Matrix.toLin_toMatrix b b A.toLinearMap

theorem deriv2_transverse_determinantRoot_le_of_jacobi
    [CompleteSpace E] (b : OrthonormalBasis (Fin (m + 1)) ℝ E)
    {J V K : ℝ → E →L[ℝ] E} {a t κ : ℝ}
    (hm : 0 < m)
    (hJ : ∀ s ∈ Set.Icc 0 a, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 a, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 a, LinearMap.IsSymmetric (K s).toLinearMap)
    (hrad : ∀ s ∈ Set.Icc 0 a, K s (b 0) = 0)
    (hzero : J 0 = 0) (ht : t ∈ Set.Ioo 0 a)
    (hpos : 0 < ((LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).submatrix
      Fin.succ Fin.succ).det)
    (hRic : -(m : ℝ) * κ ≤
      ((LinearMap.toMatrix b.toBasis b.toBasis (K t).toLinearMap).submatrix
        Fin.succ Fin.succ).trace) :
    deriv (deriv (fun s =>
      ((LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det ^ (1 / (m : ℝ)))) t ≤
      κ * ((LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).submatrix
        Fin.succ Fin.succ).det ^ (1 / (m : ℝ)) := by
  let c := EuclideanSpace.basisFun (Fin m) ℝ
  have ht' : t ∈ Set.Icc 0 a := ⟨ht.1.le, ht.2.le⟩
  have hJT (s : ℝ) (hs : s ∈ Set.Icc 0 a) := hasDerivAt_transverseOperator b (hJ s hs)
  have hVT (s : ℝ) (hs : s ∈ Set.Icc 0 a) :
      HasDerivAt (fun r => transverseOperator b (V r))
        (-((transverseOperator b (K s)).comp (transverseOperator b (J s)))) s := by
    simpa only [transverseOperator_neg, transverseOperator_comp b _ _ (hrad s hs)] using
      hasDerivAt_transverseOperator b (hV s hs)
  have hd : ContinuousAt (fun s =>
      ((LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).submatrix
        Fin.succ Fin.succ).det) t :=
    (Poincare.Matrix.differentiableAt_det (G := fun s =>
      (LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).submatrix Fin.succ Fin.succ)
      (fun i j => (hasDerivAt_toMatrix_operator b (hJ t ht') i.succ j.succ).differentiableAt)).continuousAt
  have hi : ∀ᶠ s in 𝓝 t, (transverseOperator b (J s)).IsInvertible := by
    filter_upwards [hd (Ioi_mem_nhds hpos)] with s hs
    apply isInvertible_of_toMatrix_det_ne_zero c.toBasis
    simpa only [c, toMatrix_transverseOperator] using hs.ne'
  simpa only [c, toMatrix_transverseOperator, Fintype.card_fin] using
    deriv2_determinantRoot_le_of_jacobi c
      (J := fun s => transverseOperator b (J s))
      (V := fun s => transverseOperator b (V s))
      (K := fun s => transverseOperator b (K s))
      (a := a) (t := t) (κ := κ) (by simpa using hm) hJT hVT
      (fun s hs => isSymmetric_transverseOperator b (K s) (hK s hs))
      (by simp [hzero]) ht hi (by simpa only [c, toMatrix_transverseOperator] using hpos)
      (by simpa only [c, toMatrix_transverseOperator, Fintype.card_fin] using hRic)

end PoincareConjecture.RiemannianMetric
