import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.Scalar.Trace
import PoincareConjecture.Proofs.M28.Generalized.ShortPaths











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem LeviCivitaData.six_mul_le_scalar_of_orthonormal_sectional_lower
    (D : LeviCivitaData g) (x : M) {a : ℝ}
    (hsec : ∀ v w, LeviCivitaData.IsOrthonormalPair g x v w →
      a ≤ D.sectionalCurvature x v w) :
    6 * a ≤ D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let b := (g.orthonormalBasis x).reindex (finCongr hdim)
  have hb (i j : Fin 3) : g.inner x (b i) (b j) = if i = j then 1 else 0 := by
    change inner ℝ (b i) (b j) = _
    exact b.inner_eq_ite i j
  have hdiag (i : Fin 3) : D.curvatureTensor x (b i) (b i) (b i) (b i) = 0 := by
    have h := D.curvatureTensor_swap_first x (b i) (b i) (b i) (b i)
    linarith
  have hterm (i j : Fin 3) : (if i = j then 0 else a) ≤
      D.curvatureTensor x (b i) (b j) (b i) (b j) := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true, hdiag, le_refl]
    · have hp : LeviCivitaData.IsOrthonormalPair g x (b i) (b j) :=
        ⟨by simp only [hb, ite_true], by simp only [hb, ite_true],
          by simp only [hb, hij, ite_false]⟩
      have h := hsec (b i) (b j) hp
      simpa only [LeviCivitaData.sectionalCurvature, hb, hij, ite_false,
        ite_true, mul_one, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using h
  calc
    6 * a = ∑ i : Fin 3, ∑ j : Fin 3, if i = j then 0 else a := by
      simp [Fin.sum_univ_succ]
      ring
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        D.curvatureTensor x (b i) (b j) (b i) (b j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = D.scalarCurvature x := (D.scalarCurvature_eq_sum_orthonormalBasis x b).symm




theorem SingularCComponent.six_mul_scalar_le
    {D : LeviCivitaData g} {C : ℝ} (N : SingularCComponent g D C)
    (hR : ContinuousOn D.scalarCurvature N.carrier)
    {x y : M} (hx : x ∈ N.carrier) (hy : y ∈ N.carrier) :
    6 * D.scalarCurvature y ≤ C * D.scalarCurvature x := by
  have hbounded : BddAbove (range (fun z : N.carrier => D.scalarCurvature z.1)) := by
    obtain ⟨B, hB⟩ := N.compact.bddAbove_image hR
    refine ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hB ⟨z.1, z.2, rfl⟩
  have hySup : D.scalarCurvature y ≤ scalarCurvatureSupOn g D N.carrier :=
    le_csSup hbounded ⟨⟨y, hy⟩, rfl⟩
  have htrace := D.six_mul_le_scalar_of_orthonormal_sectional_lower x
    (fun v w hvw => (N.sectional_lower x hx v w hvw).le)
  calc
    6 * D.scalarCurvature y ≤ 6 * scalarCurvatureSupOn g D N.carrier := by
      gcongr
    _ = (6 * (C⁻¹ * scalarCurvatureSupOn g D N.carrier)) * C := by
      field_simp [ne_of_gt N.constant_pos]
    _ ≤ D.scalarCurvature x * C := mul_le_mul_of_nonneg_right htrace N.constant_pos.le
    _ = C * D.scalarCurvature x := mul_comm _ _




theorem SingularCComponent.preconnected_subset
    {D : LeviCivitaData g} {C : ℝ} (N : SingularCComponent g D C)
    {S : Set M} (hS : IsPreconnected S) (hSN : (S ∩ N.carrier).Nonempty) :
    S ⊆ N.carrier := by
  obtain ⟨z, hzS, hzN⟩ := hSN
  rw [N.component_eq] at hzN ⊢
  rw [connectedComponent_eq hzN]
  exact hS.subset_connectedComponent hzS




theorem GeneralizedRicciFlowData.not_singularCComponent_on_path
    (F : GeneralizedRicciFlowData.{u}) (P : RicciFlowCurvatureTheory.{u})
    (t C : ℝ) {a b : ℝ} (hab : a ≤ b)
    (γ : ℝ → (F.slice t).carrier) (hγ : ContinuousOn γ (Icc a b))
    (hlarge : C * F.scalar ⟨t, γ a⟩ < 6 * F.scalar ⟨t, γ b⟩)
    {s : ℝ} (hs : s ∈ Icc a b)
    (N : SingularCComponent (F.metric t) (F.connection t) C) :
    γ s ∉ N.carrier := by
  intro hsN
  have hsub : γ '' Icc a b ⊆ N.carrier := N.preconnected_subset
    (isPreconnected_Icc.image γ hγ) ⟨γ s, mem_image_of_mem γ hs, hsN⟩
  have hbound := N.six_mul_scalar_le (F.continuous_scalar_slice P t).continuousOn
    (hsub (mem_image_of_mem γ (left_mem_Icc.mpr hab)))
    (hsub (mem_image_of_mem γ (right_mem_Icc.mpr hab)))
  exact (not_lt_of_ge hbound) hlarge

end PoincareConjecture
