import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.FilledModel

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_ambient_ball_of_global_saddle_matching
    {g : S2 → E3}
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : H '' range g = shear '' sphere (0 : E3) 1) :
    ∃ B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B '' sphere (0 : E3) 1 = range g := by
  refine ⟨shear.trans H.symm, ?_⟩
  rw [Diffeomorph.coe_trans, image_comp]
  rw [← hH]
  exact H.toEquiv.symm_image_image (range g)

end Poincare.Manifold.Schoenflies.Saddle
