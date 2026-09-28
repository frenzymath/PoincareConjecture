import PoincareConjecture.Definitions.M11TimeInterval
import Mathlib.Analysis.Calculus.TangentCone.Real



set_option autoImplicit false

open Set

namespace PoincareConjecture


theorem uniqueDiffWithinAt_of_spacetimeInterval
    (I : SpacetimeInterval) (t : I.domain) :
    UniqueDiffWithinAt ℝ I.domain (t : ℝ) := by
  obtain ⟨a, ha, b, hb, hab⟩ := I.nontrivial
  rcases lt_or_gt_of_ne hab with hab' | hba
  · let m : ℝ := (a + b) / 2
    have hm : m ∈ Set.Ioo a b := by
      dsimp [m]
      constructor <;> linarith
    have hsubset : Set.Ioo a b ⊆ I.domain :=
      Ioo_subset_Icc_self.trans (I.ordConnected.out ha hb)
    have hinterior : (interior I.domain).Nonempty := by
      refine ⟨m, (mem_interior_iff_mem_nhds).2 ?_⟩
      exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hm) hsubset
    exact uniqueDiffWithinAt_convex I.ordConnected.convex hinterior
      (subset_closure t.property)
  · let m : ℝ := (b + a) / 2
    have hm : m ∈ Set.Ioo b a := by
      dsimp [m]
      constructor <;> linarith
    have hsubset : Set.Ioo b a ⊆ I.domain :=
      Ioo_subset_Icc_self.trans (I.ordConnected.out hb ha)
    have hinterior : (interior I.domain).Nonempty := by
      refine ⟨m, (mem_interior_iff_mem_nhds).2 ?_⟩
      exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hm) hsubset
    exact uniqueDiffWithinAt_convex I.ordConnected.convex hinterior
      (subset_closure t.property)

end PoincareConjecture
