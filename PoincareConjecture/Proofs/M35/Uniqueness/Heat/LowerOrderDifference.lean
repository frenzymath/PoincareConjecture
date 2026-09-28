import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletVectorLowerOrder









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem dirichletValueMultiplier_sub (K : Set V) (a b : 𝓢(V, ℝ)) :
    dirichletValueMultiplier K (a - b) =
      dirichletValueMultiplier K a - dirichletValueMultiplier K b := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change schwartzMultiplier (a - b) (u : Lp ℝ 2 volume) =
    schwartzMultiplier a (u : Lp ℝ 2 volume) - schwartzMultiplier b (u : Lp ℝ 2 volume)
  rw [schwartzMultiplier_sub, sub_apply]

theorem dirichletLowerOrder_sub {K : Set V} (hK : IsClosed K)
    (B B' : Fin n → 𝓢(V, ℝ)) (C C' : 𝓢(V, ℝ)) :
    dirichletLowerOrder hK (fun i => B i - B' i) (C - C') =
      dirichletLowerOrder hK B C - dirichletLowerOrder hK B' C' := by
  simp only [dirichletLowerOrder, dirichletValueMultiplier_sub,
    ContinuousLinearMap.sub_comp, Finset.sum_sub_distrib]
  abel

theorem finiteHilbertMatrix_sub {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A B : Fin m → Fin m → E →L[ℝ] F) :
    finiteHilbertMatrix (fun i j => A i j - B i j) =
      finiteHilbertMatrix A - finiteHilbertMatrix B := by
  simp only [finiteHilbertMatrix, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub, Finset.sum_sub_distrib]

theorem norm_dirichletVectorLowerOrder_sub_le {K : Set V} (hK : IsClosed K)
    (B B' : Fin m → Fin m → Fin n → 𝓢(V, ℝ)) (C C' : Fin m → Fin m → 𝓢(V, ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hB : ∀ i j k x, ‖B i j k x - B' i j k x‖ ≤ M)
    (hC : ∀ i j x, ‖C i j x - C' i j x‖ ≤ M) :
    ‖dirichletVectorLowerOrder hK B C - dirichletVectorLowerOrder hK B' C'‖ ≤
      (m : ℝ) ^ 2 * (((n : ℝ) + 1) * M) := by
  have he : dirichletVectorLowerOrder hK (fun i j k => B i j k - B' i j k)
      (fun i j => C i j - C' i j) =
        dirichletVectorLowerOrder hK B C - dirichletVectorLowerOrder hK B' C' := by
    simp only [dirichletVectorLowerOrder, dirichletLowerOrder_sub, finiteHilbertMatrix_sub]
  rw [← he]
  exact norm_dirichletVectorLowerOrder_le hK _ _ hM hB hC

end PoincareConjecture.M35.Uniqueness.Heat
