import PoincareConjecture.Proofs.M04.SectionalRayleigh

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M34

open M04

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem six_mul_sectional_lower_le_scalar (D : LeviCivitaData g) (x : M) (k : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 3) x,
      k * metricGram g x u v ≤ D.curvatureTensor x u v u v) :
    6 * k ≤ D.scalarCurvature x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 3) x)
  have hdim : d = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  have hinner (i j : Fin d) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hgram (i j : Fin d) : metricGram g x (b i) (b j) = if i = j then 0 else 1 := by
    simp only [metricGram, hinner, ite_true, one_mul]
    split_ifs <;> norm_num
  have hsum : (∑ i : Fin d, ∑ j : Fin d, k * metricGram g x (b i) (b j)) = 6 * k := by
    calc
      _ = ∑ i : Fin d, ∑ j : Fin d, (k - if i = j then k else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hgram]
        split_ifs <;> ring
      _ = _ := by
        simp [Finset.sum_sub_distrib, hdim]
        ring
  rw [← hsum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsec (b i) (b j)

end PoincareConjecture.M34
