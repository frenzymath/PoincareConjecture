import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelOrientation

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem every_terminal_geometry_has_unmatched_slice_of_one_lower_end
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (hcount : Nat.card d.ends.LowerCutIndex = 1) :
    ∀ d' : TerminalSaddleGeometry M P p e,
      ∃ z ∈ d'.I, ¬ ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        Q '' d'.A z = d'.B z := by
  intro d'
  exact exists_unmatched_terminal_slice_of_one_lower_end hg d' hunique hform
    (one_lower_end_independent_of_terminal_geometry hg d d' hunique hcount)

theorem no_terminal_matching_choice_of_one_lower_end
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (hcount : Nat.card d.ends.LowerCutIndex = 1) :
    ¬ ∃ data : TerminalSaddleData M P p e,
      ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ∀ z ∈ data.toTerminalSaddleGeometry.I,
          Q z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z := by
  rintro ⟨data, Q, hQ⟩
  obtain ⟨z, hz, hnot⟩ := every_terminal_geometry_has_unmatched_slice_of_one_lower_end
    hg d hunique hform hcount data.toTerminalSaddleGeometry
  exact hnot ⟨Q z, hQ z hz⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
