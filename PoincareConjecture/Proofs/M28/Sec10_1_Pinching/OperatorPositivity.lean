import PoincareConjecture.Proofs.M28.Sec10_1_Pinching.GramLowerBound
import PoincareConjecture.Definitions.Ch04.Harnack

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Curvature.Operator
open scoped Manifold ContDiff Bundle BigOperators Matrix

namespace PoincareConjecture.M28

private theorem skew_product_sum (f A : Fin 3 → Fin 3 → ℝ)
    (hf : ∀ i j, f i j = -f j i) (hA : ∀ i j, A i j = -A j i) :
    (∑ i, ∑ j, f i j * A i j) =
      2 * ∑ a, f (pairFirst a) (pairSecond a) * A (pairFirst a) (pairSecond a) := by
  have hdiag (i) : f i i = 0 := by linarith [hf i i]
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.succ_zero_eq_one, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_one_eq_two, hdiag, zero_mul,
    zero_add, add_zero, pairFirst, pairSecond, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Finset.sum_const, Finset.card_singleton, one_smul]
  rw [hf 1 0, hf 0 2, hf 2 1, hA 1 0, hA 0 2, hA 2 1]
  ring

theorem skew_curvature_contraction_eq_four_rayleigh
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (A : Fin 3 → Fin 3 → ℝ) (hA : ∀ i j, A i j = -A j i) :
    let w : EuclideanSpace ℝ (Fin 3) :=
      WithLp.toLp 2 (fun i => A (pairFirst i) (pairSecond i))
    (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l) =
      4 * inner ℝ w (curvatureOperator R w) := by
  let w : EuclideanSpace ℝ (Fin 3) :=
    WithLp.toLp 2 (fun i => A (pairFirst i) (pairSecond i))
  have hlastsum (i j) := skew_product_sum (R i j) A (hlast i j) hA
  have hfirstsum (a) := skew_product_sum
    (fun i j => R i j (pairFirst a) (pairSecond a)) A
    (fun i j => hfirst i j (pairFirst a) (pairSecond a)) hA
  calc
    (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l) =
        ∑ i, ∑ j, A i j * (∑ k, ∑ l, R i j k l * A k l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = 2 * ∑ a, (∑ i, ∑ j, R i j (pairFirst a) (pairSecond a) * A i j) *
        A (pairFirst a) (pairSecond a) := by
      simp_rw [hlastsum]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      ring
    _ = 4 * inner ℝ w (curvatureOperator R w) := by
      simp_rw [hfirstsum]
      rw [curvatureOperator_rayleigh]
      simp only [dotProduct, Matrix.mulVec, curvatureMatrix, w,
        Fin.sum_univ_succ, Fin.sum_univ_zero]
      ring

end PoincareConjecture.M28

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem nonnegativeCurvatureOperator_of_plane_nonneg
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (hsec : ∀ u v : TangentSpace (𝓡 3) x, 0 ≤ D.curvatureTensor x u v u v) :
    D.NonnegativeCurvatureOperator x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let e := finCongr hdim
  let b := (g.orthonormalBasis x).reindex e
  have hpair : IsOrthonormalPair g x (b 0) (b 1) := by
    change inner ℝ (b 0) (b 0) = 1 ∧ inner ℝ (b 1) (b 1) = 1 ∧
      inner ℝ (b 0) (b 1) = 0
    norm_num [b.inner_eq_ite]
  have hleast : 0 ≤ D.leastSectionalCurvature x := by
    apply le_csInf
      (show {k : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
        IsOrthonormalPair g x u v ∧ k = D.curvatureTensor x u v u v}.Nonempty from
        ⟨_, b 0, b 1, hpair, rfl⟩)
    rintro _ ⟨u, v, _, rfl⟩
    exact hsec u v
  let R := fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hfirst : ∀ i j k l, R i j k l = -R j i k l := by
    intro i j k l
    dsimp only [R]
    rw [(hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1,
      (hD.2.2.2.1 x (b k) (b l) (b i) (b j)).1,
      (hD.2.2.2.1 x (b k) (b l) (b j) (b i)).2.1]
  have hlast : ∀ i j k l, R i j k l = -R i j l k :=
    fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).1
  have hT := curvatureOperator_isSymmetric R
    (fun i j k l => (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1)
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have heig : 0 ≤ hT.eigenvalues hn 2 := by
    rw [← D.leastSectionalCurvature_eq_operator_eigenvalue hD x b]
    exact hleast
  have hpos (w : EuclideanSpace ℝ (Fin 3)) : 0 ≤ inner ℝ w (curvatureOperator R w) := by
    rw [Poincare.symmetric_rayleigh_eq_sum_eigenvalues hT hn]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (heig.trans (hT.eigenvalues_antitone hn (by omega))) (sq_nonneg _)
  intro A hA
  let A' : Fin 3 → Fin 3 → ℝ := fun i j => A (e.symm i) (e.symm j)
  have hA' : ∀ i j, A' i j = -A' j i := fun i j => hA (e.symm i) (e.symm j)
  have hreindex : curvatureOperatorQuadratic D x A =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        A' i j * A' k l * R i j k l := by
    unfold curvatureOperatorQuadratic
    rw [← Equiv.sum_comp e.symm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp e.symm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Equiv.sum_comp e.symm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Equiv.sum_comp e.symm]
    apply Finset.sum_congr rfl
    intro l _
    simp only [A', R, b, OrthonormalBasis.reindex_apply]
  rw [hreindex]
  rw [M28.skew_curvature_contraction_eq_four_rayleigh R hfirst hlast A' hA']
  exact mul_nonneg (by norm_num) (hpos _)

end PoincareConjecture.LeviCivitaData
