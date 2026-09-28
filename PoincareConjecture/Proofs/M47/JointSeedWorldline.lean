import PoincareConjecture.Proofs.M47.JointSeedReciprocal
import PoincareConjecture.Proofs.M47.ComponentEstimateMinimum

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem jointSeed_compact_low_point_gap
    (P : M47ScalarPersistencePredecessors.{u}) [CompactSpace M]
    {J : Set ℝ} (F : RicciFlow 3 M J) {s t C L : ℝ} (q : M)
    (hst : s ≤ t) (hJ : Icc s t ⊆ J) (hC : 1 ≤ C)
    (hscalar : ∀ p : M, 0 ≤ (F.connection s).scalarCurvature p)
    (hterminal : C * (F.connection t).scalarCurvature q ≤ L)
    (hhigh : L < (F.connection s).scalarCurvature q) :
    ∃ p : M, (C / 6) * (F.connection s).scalarCurvature p ≤
      (F.connection s).scalarCurvature q := by
  obtain ⟨p, _hp, hpScalar⟩ := exists_earlier_component_scalar_le P F (U := univ)
    isCompact_univ isOpen_univ hst hJ (mem_univ q)
  have hCpos : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  refine ⟨p, ?_⟩
  calc
    _ ≤ C * (F.connection s).scalarCurvature p :=
      mul_le_mul_of_nonneg_right (by linarith) (hscalar p)
    _ ≤ C * (F.connection t).scalarCurvature q :=
      mul_le_mul_of_nonneg_left hpScalar hCpos
    _ ≤ L := hterminal
    _ ≤ _ := hhigh.le

theorem jointSeed_worldline_of_evolution_bound
    (P : M47ScalarPersistencePredecessors.{u})
    {J : Set ℝ} (F : RicciFlow 3 M J) {a b A L : ℝ} (q : M)
    (hab : a ≤ b) (hJ : Icc a b ⊆ J) (hA : 0 ≤ A) (hL : 0 < L)
    (hterminal : (F.connection b).scalarCurvature q ≤ L)
    (hestimate : ∀ s ∈ Ioo a b, L < (F.connection s).scalarCurvature q →
      |(F.connection s).laplacian (F.connection s).scalarCurvature q +
          2 * (F.connection s).ricciNormSq q| ≤
        A * (F.connection s).scalarCurvature q ^ 2)
    (hshort : A * L * (b - a) ≤ 1 / 4) :
    ∀ s ∈ Icc a b, (F.connection s).scalarCurvature q ≤ 4 * L / 3 := by
  have hcont : ContinuousOn (fun s => (F.connection s).scalarCurvature q) (Icc a b) := by
    intro s hs
    exact (P.scalar_evolution M J F s (hJ hs) q).continuousWithinAt.mono hJ
  apply jointSeed_backward_scalar_comparison
    (u := fun s => (F.connection s).scalarCurvature q) (a := a) (b := b) (A := A) (L := L)
    hab hA hL hcont hterminal ?_ hshort
  intro s hs hhigh
  refine ⟨(F.connection s).laplacian (F.connection s).scalarCurvature q +
    2 * (F.connection s).ricciNormSq q, ?_, hestimate s hs hhigh⟩
  exact (P.scalar_evolution M J F s (hJ (Ioo_subset_Icc_self hs)) q).hasDerivAt
    (Filter.mem_of_superset (Icc_mem_nhds hs.1 hs.2) hJ)

end PoincareConjecture.M47
