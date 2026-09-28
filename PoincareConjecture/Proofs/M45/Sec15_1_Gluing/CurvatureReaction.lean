import PoincareConjecture.Proofs.M45.Mathlib.FourTensorContraction
import PoincareConjecture.Definitions.Ch03.CurvatureReaction









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M45

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



noncomputable def curvatureBfour (D : LeviCivitaData g) (x : M)
    (v : Fin 4 → TangentSpace (𝓡 n) x) : ℝ :=
  D.curvatureB x (v 0) (v 1) (v 2) (v 3) -
    D.curvatureB x (v 0) (v 1) (v 3) (v 2) -
    D.curvatureB x (v 0) (v 3) (v 1) (v 2) +
    D.curvatureB x (v 0) (v 2) (v 1) (v 3)



theorem curvatureReaction_eq_Bfour_sub_slots
    (D : LeviCivitaData g) (x : M) (v : Fin 4 → TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    D.curvatureReaction x (v 0) (v 1) (v 2) (v 3) =
      2 * curvatureBfour D x v -
        ∑ j : Fin 4, ∑ l : Fin d,
          D.ricci x (v j) (b l) *
            D.riemannEvaluation x (Function.update v j (b l)) := by
  classical
  simp [LeviCivitaData.curvatureReaction, curvatureBfour,
    Fin.sum_univ_four, LeviCivitaData.riemannEvaluation,
    Finset.sum_add_distrib, Function.update]



theorem curvature_energy_reaction_le
    (D : LeviCivitaData g) (x : M) :
    let b := g.orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    4 * (∑ a : Fin 4 → Fin d,
      D.riemannEvaluation x (fun i => b (a i)) *
        curvatureBfour D x (fun i => b (a i))) ≤
      16 * (D.curvatureTensorNorm x) ^ 3 := by
  classical
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let R (i j k l : Fin d) := D.curvatureTensor x (b i) (b j) (b k) (b l)
  let B (i j k l : Fin d) := D.curvatureB x (b i) (b j) (b k) (b l)
  let N := D.curvatureTensorNorm x
  have hnorm : (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) = N ^ 2 := by
    symm
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : (∑ i, ∑ j, ∑ k, ∑ l, B i j k l ^ 2) ≤ N ^ 4 := by
    have h := curvature_contraction_sq_le R
    rw [hnorm] at h
    change (∑ i, ∑ j, ∑ k, ∑ l, (∑ p, ∑ q, R i p j q * R k p l q) ^ 2) ≤ N ^ 4
    nlinarith only [h]
  have hR : (∑ a : Fin 4 → Fin d, R (a 0) (a 1) (a 2) (a 3) ^ 2) = N ^ 2 := by
    rw [Fintype.sum_fun_fin_four]
    exact hnorm
  have h₁ : (∑ a : Fin 4 → Fin d, B (a 0) (a 1) (a 2) (a 3) ^ 2) ≤ N ^ 4 := by
    rw [Fintype.sum_fun_fin_four]
    exact hB
  have h₂ : (∑ a : Fin 4 → Fin d, B (a 0) (a 1) (a 3) (a 2) ^ 2) ≤ N ^ 4 := by
    rw [Fintype.sum_fun_fin_four]
    change (∑ i, ∑ j, ∑ k, ∑ l, B i j l k ^ 2) ≤ N ^ 4
    have heq : (∑ i, ∑ j, ∑ k, ∑ l, B i j l k ^ 2) =
        ∑ i, ∑ j, ∑ k, ∑ l, B i j k l ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    rw [heq]
    exact hB
  have h₃ : (∑ a : Fin 4 → Fin d, B (a 0) (a 3) (a 1) (a 2) ^ 2) ≤ N ^ 4 := by
    rw [Fintype.sum_fun_fin_four]
    change (∑ i, ∑ j, ∑ k, ∑ l, B i l j k ^ 2) ≤ N ^ 4
    have heq : (∑ i, ∑ j, ∑ k, ∑ l, B i l j k ^ 2) =
        ∑ i, ∑ j, ∑ k, ∑ l, B i j k l ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ j, ∑ l, ∑ k, B i l j k ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [heq]
    exact hB
  have h₄ : (∑ a : Fin 4 → Fin d, B (a 0) (a 2) (a 1) (a 3) ^ 2) ≤ N ^ 4 := by
    rw [Fintype.sum_fun_fin_four]
    change (∑ i, ∑ j, ∑ k, ∑ l, B i k j l ^ 2) ≤ N ^ 4
    have heq : (∑ i, ∑ j, ∑ k, ∑ l, B i k j l ^ 2) =
        ∑ i, ∑ j, ∑ k, ∑ l, B i j k l ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    rw [heq]
    exact hB
  exact four_contraction_energy_le
    (fun a : Fin 4 → Fin d => R (a 0) (a 1) (a 2) (a 3))
    (fun a => B (a 0) (a 1) (a 2) (a 3))
    (fun a => B (a 0) (a 1) (a 3) (a 2))
    (fun a => B (a 0) (a 3) (a 1) (a 2))
    (fun a => B (a 0) (a 2) (a 1) (a 3))
    (Real.sqrt_nonneg _) hR h₁ h₂ h₃ h₄

end PoincareConjecture.M45
