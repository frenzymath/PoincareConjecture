import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false
open scoped Bundle Topology
open Bundle Set

universe u v w

namespace PoincareConjecture.Proofs.M03

theorem exists_compact_bundle_coordinate_bound
    {B : Type u} [TopologicalSpace B]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : B → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    (a b : B) {K : Set B} (hK : IsCompact K)
    (hKa : K ⊆ (trivializationAt F E a).baseSet)
    (hKb : K ⊆ (trivializationAt F E b).baseSet) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ v : E x,
      ‖((trivializationAt F E a) (TotalSpace.mk' F x v)).2‖ ^ 2 ≤
        C * ‖((trivializationAt F E b) (TotalSpace.mk' F x v)).2‖ ^ 2 := by
  let ea := trivializationAt F E a
  let eb := trivializationAt F E b
  let P : B → F →L[ℝ] F := fun x => eb.coordChangeL ℝ ea x
  have hP : ContinuousOn P K :=
    (continuousOn_coordChange ℝ eb ea).mono (fun x hx => ⟨hKb hx, hKa hx⟩)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hP
  refine ⟨(max D 0) ^ 2, sq_nonneg _, ?_⟩
  intro x hx v
  have heq : P x (eb (TotalSpace.mk' F x v)).2 = (ea (TotalSpace.mk' F x v)).2 := by
    change eb.coordChangeL ℝ ea x (eb (TotalSpace.mk' F x v)).2 =
      (ea (TotalSpace.mk' F x v)).2
    rw [Trivialization.coordChangeL_apply eb ea ⟨hKb hx, hKa hx⟩,
      eb.symm_apply_apply_mk (hKb hx) v]
  have hnorm : ‖(ea (TotalSpace.mk' F x v)).2‖ ≤
      max D 0 * ‖(eb (TotalSpace.mk' F x v)).2‖ := by
    rw [← heq]
    exact ((P x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((hD x hx).trans (le_max_left _ _)) (norm_nonneg _))
  calc
    ‖(ea (TotalSpace.mk' F x v)).2‖ ^ 2 ≤
        (max D 0 * ‖(eb (TotalSpace.mk' F x v)).2‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (max D 0) ^ 2 * ‖(eb (TotalSpace.mk' F x v)).2‖ ^ 2 := mul_pow _ _ _

end PoincareConjecture.Proofs.M03
