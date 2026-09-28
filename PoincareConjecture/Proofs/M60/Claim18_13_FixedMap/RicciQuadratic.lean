import PoincareConjecture.Proofs.M04.TensorNormBounds
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Statements.Ch01.CurvatureCalculus
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Logic.Equiv.Fin.Basic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem m60Ricci_tensorNorm_sq (D : LeviCivitaData g) (x : M) :
    (g.tensorNorm D.ricciEvaluation x) ^ 2 = D.ricciNormSq x := by
  let b := g.orthonormalBasis x
  let k := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  unfold RiemannianMetric.tensorNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  change (∑ a : Fin 2 → k, (D.ricci x (b (a 0)) (b (a 1))) ^ 2) =
    ∑ i : k, ∑ j : k, (D.ricci x (b i) (b j)) ^ 2
  simpa [Fintype.sum_prod_type] using
    (finTwoArrowEquiv k).sum_comp (fun p : k × k => (D.ricci x (b p.1) (b p.2)) ^ 2)



theorem m60Ricci_quadratic_bound (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) {C : ℝ} (hC : 0 ≤ C)
    (hnorm : D.ricciNormSq x ≤ C ^ 2) (v : TangentSpace (𝓡 n) x) :
    |D.ricci x v v| ≤ C * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hv : 0 ≤ g.inner x v v := real_inner_self_nonneg (x := v)
  have h := M04.tensorEvaluation_sq_le_tensorNorm g hD.2.1 x ![v, v]
  rw [m60Ricci_tensorNorm_sq] at h
  simp only [LeviCivitaData.ricciEvaluation, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hv)).mp
  rw [sq_abs, mul_pow]
  simpa only [pow_two] using h.trans
    (mul_le_mul_of_nonneg_right hnorm (mul_nonneg hv hv))



theorem m60Ricci_exists_bilinear (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    ∃ B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x),
      ∀ v w, B v w = D.ricci x v w := by
  obtain ⟨A, hA⟩ := hD.2.1.1 x
  have hRic (v w : TangentSpace (𝓡 n) x) : D.ricci x v w = A ![v, w] := hA ![v, w]
  have hu0 (v w z : TangentSpace (𝓡 n) x) :
      Function.update ![v, w] 0 z = ![z, w] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hu1 (v w z : TangentSpace (𝓡 n) x) :
      Function.update ![v, w] 1 z = ![v, z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have ha1 (v w z : TangentSpace (𝓡 n) x) :
      D.ricci x (v + w) z = D.ricci x v z + D.ricci x w z := by
    simp only [hRic]
    simpa only [hu0] using A.map_update_add ![v, z] 0 v w
  have ha2 (v w z : TangentSpace (𝓡 n) x) :
      D.ricci x z (v + w) = D.ricci x z v + D.ricci x z w := by
    simp only [hRic]
    simpa only [hu1] using A.map_update_add ![z, v] 1 v w
  have hs1 (c : ℝ) (v w : TangentSpace (𝓡 n) x) :
      D.ricci x (c • v) w = c • D.ricci x v w := by
    simp only [hRic]
    simpa only [hu0] using A.map_update_smul ![v, w] 0 c v
  have hs2 (c : ℝ) (v w : TangentSpace (𝓡 n) x) :
      D.ricci x v (c • w) = c • D.ricci x v w := by
    simp only [hRic]
    simpa only [hu1] using A.map_update_smul ![v, w] 1 c w
  exact ⟨{
    toFun := fun v => {
      toFun := D.ricci x v
      map_add' := fun w z => ha2 w z v
      map_smul' := fun c w => hs2 c v w }
    map_add' := by intro v w; ext z; exact ha1 v w z
    map_smul' := by intro c v; ext w; exact hs1 c v w }, fun _ _ => rfl⟩

end PoincareConjecture
