import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Graph
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicFourierCoordinates

set_option autoImplicit false

open AddCircle MeasureTheory

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]

theorem periodicH2_secondDerivativeLp_eq
    (u : lp (fun _ : ℤ => ℂ) 2) (g : C(AddCircle L, ℂ))
    (hg : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => periodicSobolevJet (L := L) 1 1 (by omega) u (y : AddCircle L))
      (g (x : AddCircle L)) x) :
    periodicH1DerivativeLp (periodicH2JetCoordinates (L := L) 1 (by omega) u) =
      ContinuousMap.toLp 2 haarAddCircle ℂ g := by
  let f := periodicSobolevJet (L := L) 1 1 (by omega) u
  have heq : periodicH1Coordinates f g hg =
      periodicH2JetCoordinates (L := L) 1 (by omega) u := by
    apply periodicH1Decoder_injective (L := L)
    exact (periodicH1Coordinates_reconstruct f g hg).trans
      (periodicH2JetCoordinates_spec (L := L) 1 (by omega) u).2.symm
  rw [← heq]
  exact ((periodicH1Graph_spec (L := L)).2 f g hg).1

end PoincareConjecture.M63
