import PoincareConjecture.Proofs.M36.CylinderGram
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring










set_option autoImplicit false

set_option maxSynthPendingDepth 8

open scoped BigOperators

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "C" => RoundCylinderCoordinates

noncomputable def cylinderEuclideanEquiv : E₃ ≃L[ℝ] C :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ E₂).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

theorem cylinderEuclideanEquiv_basis (i : Fin 3) :
    cylinderEuclideanEquiv (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      roundCylinderCoordinateBasis i := by
  apply Prod.ext
  · apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [cylinderEuclideanEquiv, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd, PiLp.sumPiLpEquivProdLpPiLp,
        WithLp.prodContinuousLinearEquiv, WithLp.linearEquiv,
        roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single, Pi.single_apply, finSumFinEquiv, Fin.addCases]
  · fin_cases i <;>
      simp [cylinderEuclideanEquiv, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd, PiLp.sumPiLpEquivProdLpPiLp,
        WithLp.prodContinuousLinearEquiv, WithLp.linearEquiv, PiLp.equivOfUnique,
        roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single, Pi.single_apply, finSumFinEquiv, Fin.addCases]

theorem fderiv_cylinder_affine (f : C → ℝ) (c : C) (p v : E₃) :
    fderiv ℝ (fun q => f (cylinderEuclideanEquiv q + c)) p v =
      fderiv ℝ f (cylinderEuclideanEquiv p + c) (cylinderEuclideanEquiv v) := by
  change fderiv ℝ ((fun q => f (q + c)) ∘ cylinderEuclideanEquiv) p v = _
  rw [cylinderEuclideanEquiv.comp_right_fderiv, fderiv_comp_add_right]
  rfl

theorem second_fderiv_cylinder_affine (f : C → ℝ) (c : C) (p u v : E₃) :
    fderiv ℝ (fun q => fderiv ℝ
      (fun z => f (cylinderEuclideanEquiv z + c)) q u) p v =
      fderiv ℝ (fun q => fderiv ℝ f q (cylinderEuclideanEquiv u))
        (cylinderEuclideanEquiv p + c) (cylinderEuclideanEquiv v) := by
  simp only [fderiv_cylinder_affine]
  exact fderiv_cylinder_affine (fun q => fderiv ℝ f q (cylinderEuclideanEquiv u)) c p v

theorem euclideanThree_clm_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E₃ →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i : Fin 3, ‖T (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ≤ K) :
    ‖T‖ ≤ 3 * K := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  apply T.opNorm_le_bound (by positivity)
  intro x
  calc
    ‖T x‖ = ‖∑ i : Fin 3, inner ℝ (b i) x • T (b i)‖ := by
      conv_lhs => rw [← b.sum_repr' x]
      simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖inner ℝ (b i) x • T (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖x‖ * K := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      apply mul_le_mul _ (h i) (norm_nonneg _) (norm_nonneg _)
      simpa only [b.norm_eq_one, one_mul] using norm_inner_le_norm (b i) x
    _ = 3 * K * ‖x‖ := by simp; ring

theorem euclideanThree_bilinear_norm_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E₃ →L[ℝ] E₃ →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i j : Fin 3,
      ‖T (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)‖ ≤ K) :
    ‖T‖ ≤ 9 * K := by
  have hb := euclideanThree_clm_norm_le T (by positivity : 0 ≤ 3 * K)
    (fun i => euclideanThree_clm_norm_le _ hK (h i))
  nlinarith only [hb]

theorem euclideanThree_trilinear_norm_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E₃ →L[ℝ] E₃ →L[ℝ] E₃ →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i j k : Fin 3,
      ‖T (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
        (EuclideanSpace.basisFun (Fin 3) ℝ k)‖ ≤ K) :
    ‖T‖ ≤ 27 * K := by
  have hb := euclideanThree_clm_norm_le T (by positivity : 0 ≤ 9 * K)
    (fun i => euclideanThree_bilinear_norm_le _ hK (h i))
  nlinarith only [hb]

theorem euclideanThree_quadrilinear_norm_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E₃ →L[ℝ] E₃ →L[ℝ] E₃ →L[ℝ] E₃ →L[ℝ] F) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i j k l : Fin 3,
      ‖T (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
        (EuclideanSpace.basisFun (Fin 3) ℝ k) (EuclideanSpace.basisFun (Fin 3) ℝ l)‖ ≤ K) :
    ‖T‖ ≤ 81 * K := by
  have hb := euclideanThree_clm_norm_le T (by positivity : 0 ≤ 27 * K)
    (fun i => euclideanThree_trilinear_norm_le _ hK (h i))
  nlinarith only [hb]

end PoincareConjecture.M36
