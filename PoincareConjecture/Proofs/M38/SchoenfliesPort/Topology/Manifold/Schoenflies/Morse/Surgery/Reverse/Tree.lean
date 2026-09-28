import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.MorseReduction
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Reconstruction







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



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

end

end M38Schoenflies
