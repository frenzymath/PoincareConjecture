import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.MorseCoordinates.LowerHemisphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.MorseCoordinates.SquareCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2+1) := ⟨by simp⟩

theorem exists_saddle_coordinates :
    ∃ e : OpenPartialHomeomorph E2 S2,
      0 ∈ e.source ∧ e 0 = saddlePoint ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, height (e x) = -1-(x 0)^2+(x 1)^2 := by
  obtain ⟨Q, hQ0, hQzero, hQU, hQ, hQi, hform⟩ := exists_squareCoordinates_inverse
  let e := Q.trans lowerSphereChart
  have he (x : E2) : e x = lowerSphereChart (Q x) := rfl
  have hes (x : E2) (hx : x ∈ e.source) : x ∈ Q.source := hx.1
  have het (p : S2) (hp : p ∈ e.target) : lowerSphereChart.symm p ∈ Q.target := hp.2
  refine ⟨e, ⟨hQ0, hQU hQ0⟩, by rw [he, hQzero, lowerSphereChart_zero], ?_, ?_, ?_⟩
  · exact lowerSphereChart_smooth.comp (hQ.contMDiffOn.mono inter_subset_left)
      (fun _ hx => hx.2)
  · exact hQi.contMDiffOn.comp lowerSphereChart_symm_smooth.contMDiffOn
      (fun p hp => het p hp)
  · intro x hx
    rw [he, height_lowerSphereChart (hQU (hes x hx)), hform x (hes x hx)]

end Poincare.Manifold.Schoenflies.Saddle
