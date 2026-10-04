import PoincareLib.Geometry.Riemannian.Tensor.NormBounds
import Mathlib.Analysis.Matrix.PosDef

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/Mathlib/InverseGramBound.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Bilinear evaluations controlled by the inverse-Gram contraction

Morgan-Tian Definition 2.16, p. 30, uses the selected metric to
contract every tensor slot. For a positive Gram matrix, the literal
rank-two contraction controls every bilinear evaluation with constant
one. No symmetry assumption on the tensor is needed.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace Matrix

-- The selected matrix norm uses the same real scalar operations as the tensor API.
set_option backward.isDefEq.respectTransparency false in
/-- The exact inverse-Gram tensor norm bounds any bilinear evaluation
(MT Definition 2.16, p. 30, used for necks in Definition 2.18, p. 31). -/
theorem abs_bilinear_apply_le_inverse_gram_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : G.PosDef) (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ y)| ≤
      Real.sqrt (∑ a : Fin 2 → ι, ∑ b : Fin 2 → ι,
        (∏ j : Fin 2, G⁻¹ (a j) (b j)) * A (a 0) (a 1) * A (b 0) (b 1)) *
        Real.sqrt (x ⬝ᵥ (G *ᵥ x)) * Real.sqrt (y ⬝ᵥ (G *ᵥ y)) := by
  let := G.toNormedAddCommGroup hG
  let := G.toSeminormedAddCommGroup hG.posSemidef
  let := G.toInnerProductSpace hG.posSemidef
  have hin (v w : ι → ℝ) : inner ℝ v w = v ⬝ᵥ (G *ᵥ w) := by
    change (G *ᵥ w) ⬝ᵥ star v = v ⬝ᵥ (G *ᵥ w)
    rw [star_trivial, dotProduct_comm]
  let T : MultilinearMap ℝ (fun _ : Fin 2 => ι → ℝ) ℝ :=
    { toFun := fun z => z 0 ⬝ᵥ (A *ᵥ z 1)
      map_update_add' := by
        intro _ z i a b
        fin_cases i <;> simp [add_dotProduct, mulVec_add, dotProduct_add]
      map_update_smul' := by
        intro _ z i r a
        fin_cases i <;> simp [smul_dotProduct, mulVec_smul, dotProduct_smul] }
  let b := Pi.basisFun ℝ ι
  let c := stdOrthonormalBasis ℝ (ι → ℝ)
  have hgram : (Matrix.of (fun i j => inner ℝ (b i) (b j))) = G := by
    ext i j
    simp [b, hin, Pi.basisFun_apply, single_dotProduct]
  have hcoeff (a : Fin 2 → ι) : T (fun r => b (a r)) = A (a 0) (a 1) := by
    simp [T, b, Pi.basisFun_apply, single_dotProduct]
  have hcontraction := PoincareMT.multilinear_sum_mul_eq_inverse_gram T T b c
  rw [hgram] at hcontraction
  simp_rw [hcoeff] at hcontraction
  have hnorm (v : ι → ℝ) :
      @norm (ι → ℝ) (G.toNormedAddCommGroup hG).toNorm v =
        Real.sqrt (v ⬝ᵥ (G *ᵥ v)) := by
    change Real.sqrt ((G *ᵥ v) ⬝ᵥ star v) = Real.sqrt (v ⬝ᵥ (G *ᵥ v))
    rw [star_trivial, dotProduct_comm]
  have hbound := PoincareMT.abs_multilinear_apply_le_orthonormal_tensor_norm
    T c ![x, y]
  simp_rw [pow_two] at hbound
  rw [hcontraction] at hbound
  simpa only [T, MultilinearMap.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Fin.prod_univ_two, hnorm, mul_assoc] using hbound

end Matrix
