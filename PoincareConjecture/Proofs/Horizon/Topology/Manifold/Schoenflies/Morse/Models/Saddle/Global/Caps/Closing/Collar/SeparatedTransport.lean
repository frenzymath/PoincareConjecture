import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.TerminalTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.OtherCaps



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem exists_separated_terminal_collar_transport
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (i : Fin 3) :
    ∃ (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (O : Set E2) (S : Set E3),
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ (data.actualDisk i).source ∧
      T.target ⊆ (data.modelDisk i).source ∧
      IsOpen O ∧ sphere (0 : E2) 1 ⊆ O ∧
      IsCompact (closure O) ∧ closure O ⊆ T.target ∧ IsCompact S ∧
      (∀ j, j ≠ i → Disjoint S (H '' data.toTerminalSaddleGeometry.C j) ∧
        Disjoint S (data.toTerminalSaddleGeometry.modelCaps j)) ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧ EqOn G id data.toTerminalSaddleGeometry.modelBand ∧
        (∀ j, j ≠ i → EqOn G id (H '' data.toTerminalSaddleGeometry.C j) ∧
          EqOn G id (data.toTerminalSaddleGeometry.modelCaps j)) ∧
        ∀ y ∈ closure O,
          G (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i (T.symm y))))) =
            data.toTerminalSaddleGeometry.flatten
              (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) := by
  obtain ⟨N, hN, hcN, hNdis⟩ := exists_terminal_rim_neighborhood_avoiding_other_caps
    data hg Φ χ H hH hχ hplanar hlabels i
  rw [data.model_boundary i] at hcN
  obtain ⟨T, O, S, hTc, hTi, hTs, hTm, hO, hcO, hOc, hOT, hS, hSN,
      G, hfix, hband, hmap⟩ := exists_relative_terminal_collar_transport_within
    data hg Φ χ H hH hχ hplanar hlabels i hN hcN
  have hdis (j : Fin 3) (hji : j ≠ i) :
      Disjoint S (H '' data.toTerminalSaddleGeometry.C j) ∧
        Disjoint S (data.toTerminalSaddleGeometry.modelCaps j) :=
    ⟨(hNdis j hji).1.mono_left hSN, (hNdis j hji).2.mono_left hSN⟩
  refine ⟨T, O, S, hTc, hTi, hTs, hTm, hO, hcO, hOc, hOT, hS, hdis,
    G, hfix, hband, ?_, hmap⟩
  intro j hji
  constructor
  · intro z hz
    exact hfix z (fun hs => disjoint_left.mp (hdis j hji).1 hs hz)
  · intro z hz
    exact hfix z (fun hs => disjoint_left.mp (hdis j hji).2 hs hz)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
