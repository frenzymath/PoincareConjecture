import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Proofs.M04.CurvatureAlgebra

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture

theorem LeviCivitaData.scalarCurvature_pos_of_positive_sectional
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    (hpos : ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v → 0 < D.sectionalCurvature x u v) :
    0 < D.scalarCurvature x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hinner (i j) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hoff (i j) (hij : i ≠ j) : 0 < D.curvatureTensor x (b i) (b j) (b i) (b j) := by
    have hpair : LeviCivitaData.IsOrthonormalPair g x (b i) (b j) := by
      simp [LeviCivitaData.IsOrthonormalPair, hinner, hij]
    simpa [LeviCivitaData.sectionalCurvature, hinner, hij] using hpos (b i) (b j) hpair
  have hnonneg (i j) : 0 ≤ D.curvatureTensor x (b i) (b j) (b i) (b j) := by
    by_cases hij : i = j
    · subst j
      simp [LeviCivitaData.curvatureTensor, M04.curvature_self]
    · exact (hoff i j hij).le
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    simp
  let i₀ : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)) := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    norm_num [i₀, i₁] at this
  change 0 < ∑ i, ∑ j, D.curvatureTensor x (b i) (b j) (b i) (b j)
  apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j))
  exact ⟨i₀, Finset.mem_univ _, Finset.sum_pos' (fun j _ => hnonneg i₀ j)
    ⟨i₁, Finset.mem_univ _, hoff i₀ i₁ hne⟩⟩

theorem RepairedStandardCapExistenceData.scalar_pos {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {t : ℝ}
    (ht : t ∈ Set.Ico 0 E.flow.base.lifetime) (x : StandardCapSpace) :
    0 < (E.flow.connection t).scalarCurvature x := by
  by_cases ht₀ : t = 0
  · subst t
    have htransport (g h : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (hD : HEq D D') :
        D.scalarCurvature x = D'.scalarCurvature x := by
      subst h
      cases eq_of_heq hD
      rfl
    change 0 < (E.flow.base.flow.connection 0).scalarCurvature x
    rw [htransport _ _ _ _ E.flow.base.initial_metric E.flow.base.initial_connection]
    exact (inv_pos.mpr E.initial_estimate.scalar_constant_pos).trans_le
      (E.initial_estimate.scalar_bounds x).1
  · exact (E.flow.connection t).scalarCurvature_pos_of_positive_sectional x
      (E.positive_sectional t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht₀), ht.2⟩ x)

end PoincareConjecture
