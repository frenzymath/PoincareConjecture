import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular.Filling
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Minimum
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Maximum
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Cases







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

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_filling_or_saddle_core
    {f : S2 -> E3} (M : SphereMorseReduction f)
    {g : S2 -> E3} (hg : g ∈ M.tree.leaves) :
    (∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range g) ∨
    ∃ P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g,
      P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
        {p | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}) ∧
      P.PreservesCaps ∧ ∃ p ∈ interior P.core,
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) p = 0 ∧
        (∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (M.v : E3) (g y)) q = 0 -> q = p) ∧
        ∃ e : OpenPartialHomeomorph E2 S2,
          0 ∈ e.source ∧ e 0 = p ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          e.target ⊆ interior P.core ∧
          ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
            inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2 := by
  obtain ⟨P, hP, hcaps⟩ := M.tree.exists_cap_preserving_path_to_leaf hg
    M.protects_critical_values M.preserves_caps
  rcases M.terminal_core_cases hg P hP with hreg | hmin | hmax | hsaddle
  · exact Or.inl (P.exists_ambient_filling_of_regular_core
      (M.tree.embedding_of_mem_leaves hg) hcaps hreg)
  · obtain ⟨p, hp, hmin⟩ := hmin
    exact Or.inl (M.exists_ambient_filling_of_minimum_core hg P hP hcaps hp hmin)
  · obtain ⟨p, hp, hmax⟩ := hmax
    exact Or.inl (M.exists_ambient_filling_of_maximum_core hg P hP hcaps hp hmax)
  · exact Or.inr ⟨P, hP, hcaps, hsaddle⟩

end Poincare.Manifold.Schoenflies.SphereMorseReduction

end

end M38Schoenflies
