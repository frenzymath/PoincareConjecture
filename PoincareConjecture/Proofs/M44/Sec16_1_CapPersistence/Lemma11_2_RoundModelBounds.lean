import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundModelCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M44

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}

theorem scalarCurvature_eq_six_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1) (x : M) : D.scalarCurvature x = 6 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    unfold TangentSpace
    simp
  have hb (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      g.inner x (b i) (b j) = if i = j then 1 else 0 := b.inner_eq_ite i j
  change (∑ i, ∑ j, D.curvatureTensor x (b i) (b j) (b i) (b j)) = 6
  simp_rw [curvatureTensor_eq_metricGram_of_sectional_one D hsec, hb]
  norm_num [hdim, Fin.sum_univ_succ]

theorem curvatureTensorNorm_le_nine_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1) (x : M) : D.curvatureTensorNorm x ≤ 9 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    unfold TangentSpace
    simp
  have hb (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      g.inner x (b i) (b j) = if i = j then 1 else 0 := b.inner_eq_ite i j
  have hcomponent (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2 ≤ 1 := by
    rw [curvatureTensor_eq_metricGram_of_sectional_one D hsec]
    simp only [hb]
    split_ifs <;> norm_num
  change Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2) ≤ 9
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num, ?_⟩
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          ∑ _k : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
            ∑ _l : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)), (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hcomponent i j k l
    _ = 9 ^ 2 := by norm_num [hdim]

theorem curvatureDerivativeNorm_le_nine_of_sectional_one (D : LeviCivitaData g)
    (hsec : ∀ x v w, LeviCivitaData.IsOrthonormalPair g x v w →
      D.sectionalCurvature x v w = 1) (m : ℕ) (x : M) :
    D.curvatureDerivativeNorm m x ≤ 9 := by
  cases m with
  | zero =>
    rw [D.curvatureDerivativeNorm_zero]
    exact curvatureTensorNorm_le_nine_of_sectional_one D hsec x
  | succ m =>
    rw [curvatureDerivativeNorm_succ_zero_of_sectional_one D hsec]
    norm_num

end PoincareConjecture.M44
