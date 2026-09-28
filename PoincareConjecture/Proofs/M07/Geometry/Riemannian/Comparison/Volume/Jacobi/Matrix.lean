import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.Operator
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.Determinant
import Mathlib.Analysis.Matrix.Hermitian

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.RiemannianMetric

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem toMatrix_operator_inverse (b : Module.Basis ι ℝ E)
    {A : E →L[ℝ] E} (hA : A.IsInvertible) :
    LinearMap.toMatrix b b A.inverse.toLinearMap =
      (LinearMap.toMatrix b b A.toLinearMap)⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  rw [← LinearMap.toMatrix_comp b b b]
  have heq : A.inverse.toLinearMap.comp A.toLinearMap = LinearMap.id := by
    ext x
    exact hA.inverse_apply_self x
  rw [heq, LinearMap.toMatrix_id]

theorem hasDerivAt_toMatrix_operator (b : OrthonormalBasis ι ℝ E)
    {A : ℝ → E →L[ℝ] E} {A' : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) (i j : ι) :
    HasDerivAt (fun s => LinearMap.toMatrix b.toBasis b.toBasis (A s).toLinearMap i j)
      (LinearMap.toMatrix b.toBasis b.toBasis A'.toLinearMap i j) t := by
  have hv : HasDerivAt (fun s => A s (b j)) (A' (b j)) t := by
    simpa using hA.clm_apply (hasDerivAt_const t (b j))
  simpa only [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply,
    b.repr_apply_apply, inner_zero_left, add_zero] using!
    (hasDerivAt_const t (b i)).inner ℝ hv

theorem hasDerivAt_jacobi_matrix_logarithmicDerivative
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E)
    {J V : ℝ → E →L[ℝ] E} {K : E →L[ℝ] E} {t : ℝ}
    (hJ : HasDerivAt J (V t) t)
    (hV : HasDerivAt V (-(K.comp (J t))) t)
    (hinv : ∀ᶠ s in 𝓝 t, (J s).IsInvertible) :
    let j := fun s => LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap
    let v := fun s => LinearMap.toMatrix b.toBasis b.toBasis (V s).toLinearMap
    let k := LinearMap.toMatrix b.toBasis b.toBasis K.toLinearMap
    ∀ a c, HasDerivAt (fun s => (v s * (j s)⁻¹) a c)
      ((-((v t * (j t)⁻¹) * (v t * (j t)⁻¹)) - k) a c) t := by
  dsimp only
  intro a c
  have ht := Filter.Eventually.self_of_nhds hinv
  have h := hasDerivAt_toMatrix_operator b
    (hasDerivAt_jacobi_logarithmicDerivative hJ hV hinv) a c
  have heq : (fun s => (LinearMap.toMatrix b.toBasis b.toBasis (V s).toLinearMap *
      (LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap)⁻¹) a c) =ᶠ[𝓝 t]
      (fun s => LinearMap.toMatrix b.toBasis b.toBasis
        ((V s).comp (J s).inverse).toLinearMap a c) := by
    filter_upwards [hinv] with s hs
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis,
      toMatrix_operator_inverse _ hs]
  convert! h.congr_of_eventuallyEq heq using 1
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_neg,
    map_sub, map_neg, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis, toMatrix_operator_inverse _ ht]

theorem isSymm_jacobi_matrix_logarithmicDerivative
    [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E)
    {J V K : ℝ → E →L[ℝ] E} {a t : ℝ}
    (hJ : ∀ s ∈ Set.Icc 0 a, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 a, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 a, LinearMap.IsSymmetric (K s).toLinearMap)
    (hzero : J 0 = 0) (ht : t ∈ Set.Icc 0 a) (hinv : (J t).IsInvertible) :
    (LinearMap.toMatrix b.toBasis b.toBasis (V t).toLinearMap *
      (LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap)⁻¹).IsSymm := by
  have h := isSymmetric_jacobi_logarithmicDerivative hJ hV hK hzero ht hinv
  have hm := (LinearMap.isHermitian_toMatrix_iff b).mpr h
  rw [Matrix.isHermitian_iff_isSymm, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis,
    toMatrix_operator_inverse _ hinv] at hm
  exact hm

theorem deriv2_determinantRoot_le_of_jacobi
    [CompleteSpace E] (b : OrthonormalBasis ι ℝ E)
    {J V K : ℝ → E →L[ℝ] E} {a t κ : ℝ}
    (hm : 0 < Fintype.card ι)
    (hJ : ∀ s ∈ Set.Icc 0 a, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 a, HasDerivAt V (-((K s).comp (J s))) s)
    (hK : ∀ s ∈ Set.Icc 0 a, LinearMap.IsSymmetric (K s).toLinearMap)
    (hzero : J 0 = 0) (ht : t ∈ Set.Ioo 0 a)
    (hinv : ∀ᶠ s in 𝓝 t, (J s).IsInvertible)
    (hpos : 0 < (LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).det)
    (hRic : -(Fintype.card ι : ℝ) * κ ≤
      (LinearMap.toMatrix b.toBasis b.toBasis (K t).toLinearMap).trace) :
    deriv (deriv (fun s =>
      (LinearMap.toMatrix b.toBasis b.toBasis (J s).toLinearMap).det ^
        (1 / (Fintype.card ι : ℝ)))) t ≤
      κ * (LinearMap.toMatrix b.toBasis b.toBasis (J t).toLinearMap).det ^
        (1 / (Fintype.card ι : ℝ)) := by
  have ht' : t ∈ Set.Icc 0 a := ⟨ht.1.le, ht.2.le⟩
  have hi := Filter.Eventually.self_of_nhds hinv
  apply deriv2_determinantRoot_le_of_riccati hm (V := fun s =>
    LinearMap.toMatrix b.toBasis b.toBasis (V s).toLinearMap)
  · filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hasDerivAt_toMatrix_operator b (hJ s ⟨hs.1.le, hs.2.le⟩)
  · exact hpos
  · exact isSymm_jacobi_matrix_logarithmicDerivative b hJ hV hK hzero ht' hi
  · exact hasDerivAt_jacobi_matrix_logarithmicDerivative b (hJ t ht') (hV t ht') hinv
  · exact hRic

end PoincareConjecture.RiemannianMetric
