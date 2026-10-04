import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.MorseReduction
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Reconstruction

/-! # Reconstructing ball fillings through the finite surgery tree -/

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

/-- Exact reverse attachment propagates all actual leaf fillings through
the constructed finite tree, without a separate reconstruction hypothesis. -/
theorem SphereSurgeryTree.exists_ambient_ball_of_leaf_fillings
    {v : E3} {A : Finset Real} {f : S2 -> E3}
    (tree : SphereSurgeryTree v A f)
    (hleaves : ∀ g ∈ tree.leaves,
      ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : E3) 1 = range g) :
    ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B '' sphere (0 : E3) 1 = range f := by
  apply tree.induction_on_leaves
    (fun g => ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B '' sphere (0 : E3) 1 = range g) hleaves
  rintro g c R _ _ S ⟨Bminus, hminus⟩ ⟨Bplus, hplus⟩
  exact S.exists_ambient_ball_of_children Bminus Bplus hminus hplus

/-- Undoing the initial Morse perturbation gives the original sphere
image once all of its actual terminal spheres are filled. -/
theorem SphereMorseReduction.exists_ambient_ball_of_leaf_fillings
    {f : S2 -> E3} (M : SphereMorseReduction f)
    (hleaves : ∀ g ∈ M.tree.leaves,
      ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        B '' sphere (0 : E3) 1 = range g) :
    ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B '' sphere (0 : E3) 1 = range f := by
  obtain ⟨B, hB⟩ := M.tree.exists_ambient_ball_of_leaf_fillings hleaves
  refine ⟨B.trans M.D.symm, ?_⟩
  change (M.D.symm ∘ B) '' sphere (0 : E3) 1 = _
  rw [image_comp, hB, ← range_comp]
  congr 1
  funext p
  exact M.D.symm_apply_apply (f p)

end Poincare.Manifold.Schoenflies
