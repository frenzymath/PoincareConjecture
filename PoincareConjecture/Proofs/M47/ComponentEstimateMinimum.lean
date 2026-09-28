import PoincareConjecture.Statements.M47ScalarPersistence
import PoincareConjecture.Proofs.M04.CompactSlabParabolic
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem component_scalar_floor_preserved
    (P : M47ScalarPersistencePredecessors.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) {U : Set M}
    (hcompact : IsCompact U) (hopen : IsOpen U)
    {a b m : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hinit : ∀ x ∈ U, m ≤ (F.connection a).scalarCurvature x) :
    ∀ t ∈ Icc a b, ∀ x ∈ U, m ≤ (F.connection t).scalarCurvature x := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · let f : ℝ → M → ℝ := fun t x => (F.connection t).scalarCurvature x - m
    let v : ℝ → M → ℝ := fun t x =>
      (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x
    have hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ U) :=
      ((P.scalar_regular M J F).continuousOn.mono
        (prod_mono hJ (subset_univ U))).sub continuousOn_const
    have hderiv : ∀ t ∈ Icc a b, ∀ x ∈ U,
        HasDerivWithinAt (fun s => f s x) (v t x) (Icc a b) t := by
      intro t ht x _hx
      exact ((P.scalar_evolution M J F t (hJ ht) x).mono hJ).sub_const m
    have hmin : ∀ t ∈ Ioc a b, ∀ x ∈ U,
        (∀ y ∈ U, f t x ≤ f t y) → f t x < 0 → -0 * f t x ≤ v t x := by
      intro t _ht x hx hmin _hneg
      have hlocal : IsLocalMin (F.connection t).scalarCurvature x := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact (sub_le_sub_iff_right m).mp (hmin y hy)
      have hlap := (F.connection t).laplacian_nonneg_of_isLocalMin
        (M34.contMDiff_scalarCurvature (F.connection t) x) hlocal
      have hRic : 0 ≤ (F.connection t).ricciNormSq x :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      simp only [neg_zero, zero_mul]
      exact add_nonneg hlap (mul_nonneg (by norm_num) hRic)
    have h := M04.compact_subset_min_velocity_nonnegative_Icc hcompact (K := 0)
      hab f v hf hderiv hmin (fun x hx => sub_nonneg.mpr (hinit x hx))
    intro t ht x hx
    exact sub_nonneg.mp (h t ht x hx)
  · intro t ht x hx
    have heq : t = a := le_antisymm ht.2 ht.1
    subst t
    exact hinit x hx

theorem exists_earlier_component_scalar_le
    (P : M47ScalarPersistencePredecessors.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) {U : Set M}
    (hcompact : IsCompact U) (hopen : IsOpen U)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J) {x : M} (hx : x ∈ U) :
    ∃ q ∈ U, (F.connection a).scalarCurvature q ≤
      (F.connection b).scalarCurvature x := by
  obtain ⟨q, hq, hmin⟩ := hcompact.exists_isMinOn ⟨x, hx⟩
    (M34.contMDiff_scalarCurvature (F.connection a)).continuous.continuousOn
  exact ⟨q, hq, component_scalar_floor_preserved P F hcompact hopen hab hJ
    hmin b ⟨hab, le_rfl⟩ x hx⟩

end PoincareConjecture.M47
