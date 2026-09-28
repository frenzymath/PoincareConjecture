import PoincareConjecture.Statements.M64Comparison
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {mu : ℝ}

theorem m65CommonCircumference (net : M64FamilyAnnulusNet G Gamma mu)
    (cutoff : LoopTwoSphere → ℝ) (hcutoff : ∀ i, 0 < cutoff (net.nodes i)) :
    ∃ circumference : ℝ, 0 < circumference ∧ circumference < 1 ∧
      circumference < net.circumference_cutoff ∧
        ∀ i, circumference < cutoff (net.nodes i) := by
  classical
  let bounds : Finset ℝ := insert 1 (insert net.circumference_cutoff
    (Finset.univ.image (fun i => cutoff (net.nodes i))))
  have hne : bounds.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpositive : ∀ x ∈ bounds, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact net.cutoff_positive
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hcutoff i
  have hmin : 0 < bounds.min' hne := hpositive _ (Finset.min'_mem _ _)
  have hlt : ∀ x ∈ bounds, bounds.min' hne / 2 < x := by
    intro x hx
    exact (half_lt_self hmin).trans_le (Finset.min'_le _ _ hx)
  refine ⟨bounds.min' hne / 2, half_pos hmin, hlt 1 ?_,
    hlt net.circumference_cutoff ?_, fun i => hlt (cutoff (net.nodes i)) ?_⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

end PoincareConjecture
