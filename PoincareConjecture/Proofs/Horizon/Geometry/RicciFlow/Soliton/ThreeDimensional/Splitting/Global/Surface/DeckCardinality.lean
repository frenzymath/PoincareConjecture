import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse











noncomputable section
set_option autoImplicit false

open Matrix

namespace PoincareConjecture.RicciFlow.Splitting

private theorem fixed_vector_eq_zero_of_free
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hfree : ∀ x, ‖x‖ = 1 → L x ≠ x) {v : EuclideanSpace ℝ (Fin 3)}
    (hv : L v = v) : v = 0 := by
  by_contra hne
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  apply hfree (‖v‖⁻¹ • v)
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ hn]
  · rw [L.map_smul, hv]

private def orthogonalThreeMatrix
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearEquiv.toLinearMap

private theorem orthogonalThreeMatrix_one :
    orthogonalThreeMatrix (1 : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 3)) = 1 := LinearMap.toMatrix_id _

private theorem orthogonalThreeMatrix_mul
    (L K : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    orthogonalThreeMatrix (L * K) = orthogonalThreeMatrix L * orthogonalThreeMatrix K :=
  LinearMap.toMatrix_comp _ _ _ _ _

private theorem orthogonalThreeMatrix_apply
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) :
    orthogonalThreeMatrix L *ᵥ WithLp.ofLp x = WithLp.ofLp (L x) := by
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L.toLinearEquiv.toLinearMap x
  have hrepr (v : EuclideanSpace ℝ (Fin 3)) :
      ⇑((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr v) = WithLp.ofLp v := by
    funext i
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rw [hrepr x, hrepr (L.toLinearEquiv.toLinearMap x)] at h
  exact h


private theorem orthogonalThreeMatrix_det_eq_neg_one
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hfree : ∀ x, ‖x‖ = 1 → L x ≠ x) :
    (orthogonalThreeMatrix L).det = -1 := by
  let A := orthogonalThreeMatrix L
  have hA : A * A.transpose = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff _ _).mp
      (L.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin 3) ℝ)
        (EuclideanSpace.basisFun (Fin 3) ℝ))
  have hdet : (A - 1).det ≠ 0 := by
    apply isUnit_iff_ne_zero.mp
    apply (Matrix.isUnit_iff_isUnit_det (A - 1)).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    apply sub_eq_zero.mp
    have hz : (A - 1) *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have heq : A *ᵥ (x - y) = x - y := by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using hz
    have hfixed : L (WithLp.toLp 2 (x - y)) = WithLp.toLp 2 (x - y) := by
      apply WithLp.ofLp_injective
      exact (orthogonalThreeMatrix_apply L (WithLp.toLp 2 (x - y))).symm.trans heq
    exact congrArg WithLp.ofLp (fixed_vector_eq_zero_of_free L hfree hfixed)
  have htranspose : (1 - A.transpose).det = -(A - 1).det := by
    rw [← Matrix.det_transpose (1 - A.transpose)]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
    rw [show (1 : Matrix (Fin 3) (Fin 3) ℝ) - A = -(A - 1) by abel, Matrix.det_neg]
    norm_num
  have hmul : A * (1 - A.transpose) = A - 1 := by
    rw [mul_sub, mul_one, hA]
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, htranspose] at h
  have heq : (A.det + 1) * (A - 1).det = 0 := by nlinarith
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp heq).resolve_right hdet)

variable (H : Subgroup (EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)))
  (hfree : ∀ L : H, L ≠ 1 → ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → L.val x ≠ x)

private def orthogonalThreeDet : H →* ℝ where
  toFun L := (orthogonalThreeMatrix L.val).det
  map_one' := by rw [show (1 : H).val = 1 from rfl, orthogonalThreeMatrix_one, Matrix.det_one]
  map_mul' L K := by
    rw [show (L * K).val = L.val * K.val from rfl, orthogonalThreeMatrix_mul, Matrix.det_mul]

include hfree

private theorem orthogonalThreeDet_eq_one_iff (L : H) :
    orthogonalThreeDet H L = 1 ↔ L = 1 := by
  constructor
  · intro h
    by_contra hne
    have hneg := orthogonalThreeMatrix_det_eq_neg_one L.val (hfree L hne)
    change orthogonalThreeDet H L = -1 at hneg
    linarith
  · rintro rfl
    exact (orthogonalThreeDet H).map_one

private theorem orthogonalThreeDet_injective : Function.Injective (orthogonalThreeDet H) := by
  intro L K hLK
  apply inv_mul_eq_one.mp
  apply (orthogonalThreeDet_eq_one_iff H hfree _).mp
  rw [map_mul, ← hLK, ← map_mul, inv_mul_cancel, map_one]



theorem free_orthogonalThree_subgroup_card_le_two : Nat.card H ≤ 2 := by
  classical
  let f : H → Fin 2 := fun L => if L = 1 then 0 else 1
  have hf : Function.Injective f := by
    intro L K hLK
    by_cases hL : L = 1
    · by_cases hK : K = 1
      · exact hL.trans hK.symm
      · simp [f, hL, hK] at hLK
    · by_cases hK : K = 1
      · simp [f, hL, hK] at hLK
      · apply orthogonalThreeDet_injective H hfree
        exact (orthogonalThreeMatrix_det_eq_neg_one L.val (hfree L hL)).trans
          (orthogonalThreeMatrix_det_eq_neg_one K.val (hfree K hK)).symm
  simpa using Nat.card_le_card_of_injective f hf



theorem free_orthogonalThree_subgroup_eq_antipodal (L : H) (hL : L ≠ 1) :
    L.val = LinearIsometryEquiv.neg ℝ := by
  have hdet : orthogonalThreeDet H L = -1 :=
    orthogonalThreeMatrix_det_eq_neg_one L.val (hfree L hL)
  have hsq : L * L = 1 := by
    apply (orthogonalThreeDet_eq_one_iff H hfree _).mp
    rw [map_mul, hdet]
    norm_num
  have hinv (x : EuclideanSpace ℝ (Fin 3)) : L.val (L.val x) = x := by
    exact congrArg (fun K : H => K.val x) hsq
  apply LinearIsometryEquiv.ext
  intro x
  change L.val x = -x
  apply eq_neg_of_add_eq_zero_right
  apply fixed_vector_eq_zero_of_free L.val (hfree L hL)
  rw [L.val.map_add, hinv]
  exact add_comm _ _

end PoincareConjecture.RicciFlow.Splitting
