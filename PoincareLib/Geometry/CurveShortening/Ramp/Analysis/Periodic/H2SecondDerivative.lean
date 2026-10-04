import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.H1Graph
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.FourierCoordinates

/-!
# Actual second derivative of a periodic H2 trace

The full complex H1 decoder identifies the bounded second-derivative
coordinate with a supplied genuine continuous derivative. MT2007
Claim 19.1, p. 437; `2026-09-22-c2-spectral-second-derivative.md`,
statement 1.
-/

set_option autoImplicit false

open AddCircle MeasureTheory

namespace PoincareMT.M63

variable {L : ℝ} [Fact (0 < L)]

/-- The actual derivative of the first H2 jet has the bounded L2
coordinate given by the two existing derivative maps. MT2007
Claim 19.1, p. 437; second-derivative decoder derivation, statement 1. -/
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

end PoincareMT.M63
