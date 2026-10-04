import PoincareLib.Geometry.Curvature.Operator.ThreeDimensional

/-!
# Sectional evaluations in cyclic two-form coordinates

These contractions identify a four-covariant curvature tensor on a plane with
the Rayleigh value of its curvature matrix. They support Morgan--Tian,
Theorem 4.8, p. 66, and Corollary 4.33, p. 80.
-/

open scoped BigOperators Matrix

namespace Poincare.Geometry.Curvature.Operator

theorem skew_contraction_eq_crossProduct
    (f : Fin 3 → Fin 3 → ℝ) (hskew : ∀ i j, f i j = -f j i)
    (u v : Fin 3 → ℝ) :
    (∑ i, ∑ j, f i j * u i * v j) =
      ∑ a, f (pairFirst a) (pairSecond a) * crossProduct u v a := by
  have hdiag (i) : f i i = 0 := by linarith [hskew i i]
  simp [Fin.sum_univ_succ, pairFirst, pairSecond, hdiag, cross_apply]
  rw [hskew 1 0, hskew 0 2, hskew 2 1]
  ring

theorem curvature_contraction_eq_crossProduct_pairing
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (u v w z : Fin 3 → ℝ) :
    (∑ i, ∑ j, (∑ k, ∑ l, R i j k l * w k * z l) * u i * v j) =
      dotProduct (crossProduct u v)
        ((curvatureMatrix R).mulVec (crossProduct w z)) := by
  simp_rw [skew_contraction_eq_crossProduct _ (hlast _ _) w z]
  have hfirstsum (a) := skew_contraction_eq_crossProduct
    (fun i j => R i j (pairFirst a) (pairSecond a))
    (fun i j => hfirst i j _ _) u v
  calc
    (∑ i, ∑ j, (∑ a, R i j (pairFirst a) (pairSecond a) *
        crossProduct w z a) * u i * v j) =
        ∑ a, (∑ i, ∑ j, R i j (pairFirst a) (pairSecond a) * u i * v j) *
          crossProduct w z a := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      ring
    _ = dotProduct (crossProduct u v)
        ((curvatureMatrix R).mulVec (crossProduct w z)) := by
      simp_rw [hfirstsum]
      simp only [dotProduct, Matrix.mulVec, curvatureMatrix,
        Fin.sum_univ_succ, Fin.sum_univ_zero]
      ring

theorem curvature_contraction_eq_crossProduct_rayleigh
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (u v : Fin 3 → ℝ) :
    (∑ i, ∑ j, (∑ k, ∑ l, R i j k l * u k * v l) * u i * v j) =
      dotProduct (crossProduct u v)
        ((curvatureMatrix R).mulVec (crossProduct u v)) :=
  curvature_contraction_eq_crossProduct_pairing R hfirst hlast u v u v

private lemma sum_fin_cons {n : ℕ} (f : (Fin (n+1) → Fin 3) → ℝ) :
    ∑ r, f r = ∑ i, ∑ r, f (Fin.cons i r) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin 3)).sum_comp f,
    Fintype.sum_prod_type]
  rfl
theorem multilinear_curvature_expansion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (b : Fin 3 → E) (u v w z : Fin 3 → ℝ) :
    A ![∑ i, u i • b i, ∑ i, v i • b i, ∑ i, w i • b i, ∑ i, z i • b i] =
      ∑ i, ∑ j, (∑ k, ∑ l, A ![b i,b j,b k,b l] * w k * z l) * u i * v j := by
  let c : Fin 4 → Fin 3 → ℝ := ![u, v, w, z]
  have heq : ![∑ i, u i • b i, ∑ i, v i • b i, ∑ i, w i • b i, ∑ i, z i • b i] =
      (fun a : Fin 4 => ∑ i, c a i • b i) := by
    funext a
    fin_cases a <;> rfl
  rw [heq, A.map_sum]
  simp_rw [A.map_smul_univ, smul_eq_mul]
  simp only [sum_fin_cons, Fintype.sum_unique, Fin.prod_univ_succ, Fin.prod_univ_zero,
    c, Fin.cons_zero, Fin.cons_succ, mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring_nf
  congr 2
  funext a
  fin_cases a <;> rfl

theorem multilinear_plane_expansion {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (b : Fin 3 → E) (u v : Fin 3 → ℝ) :
    A ![∑ i, u i • b i, ∑ i, v i • b i, ∑ i, u i • b i, ∑ i, v i • b i] =
      ∑ i, ∑ j, (∑ k, ∑ l, A ![b i,b j,b k,b l] * u k * v l) * u i * v j :=
  multilinear_curvature_expansion A b u v u v

end Poincare.Geometry.Curvature.Operator
