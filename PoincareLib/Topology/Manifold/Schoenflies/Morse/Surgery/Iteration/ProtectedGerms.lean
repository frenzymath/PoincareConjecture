import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Tree
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Step.ProtectedHeights

/-! # Persistence of actual sphere germs throughout the finite surgery tree -/

noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryTree

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 -> E3} {v : E3} {A : Finset Real} {B : Set Real}

/-- At a protected height, a terminal embedding agrees with the original
embedding on a neighborhood of the same intrinsic sphere point. -/
theorem protected_germ_of_mem_leaves (tree : SphereSurgeryTree v A f)
    (hprotects : tree.Protects B) {g : S2 -> E3} (hg : g ∈ tree.leaves)
    {p : S2} (hp : inner Real v (g p) ∈ B) : g =ᶠ[𝓝 p] f := by
  induction tree with
  | leaf hf hav =>
    simp only [leaves, List.mem_singleton] at hg
    subst g
    exact Filter.EventuallyEq.rfl
  | branch hc hsep S minus plus ihM ihP =>
    rcases List.mem_append.mp hg with hM | hP
    · have hgm := ihM hprotects.2.1 hM
      have hpm : inner Real v (S.fMinus p) ∈ B := hgm.self_of_nhds ▸ hp
      exact hgm.trans (S.protected_minus_eventuallyEq (hprotects.1 _ hpm))
    · have hgp := ihP hprotects.2.2 hP
      have hpp : inner Real v (S.fPlus p) ∈ B := hgp.self_of_nhds ▸ hp
      exact hgp.trans (S.protected_plus_eventuallyEq (hprotects.1 _ hpp))

/-- Every original point at a protected height occurs in a terminal sphere,
with its ambient embedding germ unchanged. -/
theorem exists_protected_point_in_leaf (tree : SphereSurgeryTree v A f)
    (hprotects : tree.Protects B) {p : S2} (hp : inner Real v (f p) ∈ B) :
    ∃ g ∈ tree.leaves, g =ᶠ[𝓝 p] f := by
  induction tree with
  | leaf hf hav => exact ⟨_, by simp [leaves], Filter.EventuallyEq.rfl⟩
  | branch hc hsep S minus plus ihM ihP =>
    rcases S.protected_point_survives (hprotects.1 _ hp) with ⟨_, hM⟩ | ⟨_, hP⟩
    · have hpm : inner Real v (S.fMinus p) ∈ B := hM.self_of_nhds.symm ▸ hp
      obtain ⟨g, hg, hgm⟩ := ihM hprotects.2.1 hpm
      exact ⟨g, List.mem_append_left _ hg, hgm.trans hM⟩
    · have hpp : inner Real v (S.fPlus p) ∈ B := hP.self_of_nhds.symm ▸ hp
      obtain ⟨g, hg, hgp⟩ := ihP hprotects.2.2 hpp
      exact ⟨g, List.mem_append_right _ hg, hgp.trans hP⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryTree
