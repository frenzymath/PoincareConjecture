import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.LowerFamily
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.UpperFamily

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_supported_terminal_curved_collar_transport
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχsmooth : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ H₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, H₂ y = y) ∧ EqOn H₂ id data.toTerminalSaddleGeometry.modelBand ∧
        ∀ i, H₂ '' (H '' data.toTerminalSaddleGeometry.C i) =
          data.toTerminalSaddleGeometry.modelCaps i := by
  obtain ⟨E, hEheight, hEcore, hgerms, K, hK, F, hFfix, hFband, hFpoint, hFcap⟩ :=
    exists_prepared_horizontal_terminal_germs data hg Φ hzero hΦ hΦinv χ hχsmooth H
      hH hχ hplanar hlabels
  have hsurface : ∀ i, ∃ U : Set E3, IsOpen U ∧
      (fun x => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) ''
        sphere (0 : E2) 1 ⊆ U ∧
      (E '' range g) ∩ U =
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U := by
    intro i
    obtain ⟨U, hU, hrim, _, hsurface⟩ := hgerms i
    exact ⟨U, hU, hrim, hsurface⟩
  let c := (data.ends.lowerCut + data.ends.upperCut) / 2
  have hlc : data.ends.lowerCut < c := by dsimp [c]; linarith [data.ends.cuts_lt]
  have hcu : c < data.ends.upperCut := by dsimp [c]; linarith [data.ends.cuts_lt]
  obtain ⟨Kl, hKl, Rl, hRl, hRlfix, hRlcap⟩ :=
    exists_terminal_lower_family_replacement_of_prepared data hg Φ χ H hH hχ hplanar hlabels
      E F hEheight hEcore hFband hFpoint hsurface hlc hcu
  obtain ⟨Ku, hKu, Ru, hRu, hRufix, hRucap⟩ :=
    exists_terminal_upper_family_replacement_of_prepared data hg Φ χ H hH hχ hplanar hlabels
      E F hEheight hEcore hFband hFpoint hsurface hlc hcu
  have hRlband : EqOn Rl id (data.toTerminalSaddleGeometry.flatten ⁻¹'
      data.toTerminalSaddleGeometry.modelBand) := by
    rw [← terminal_physical_modelBand_eq_preimage]
    exact hRlfix.mono subset_union_left
  have hRuband : EqOn Ru id (data.toTerminalSaddleGeometry.flatten ⁻¹'
      data.toTerminalSaddleGeometry.modelBand) := by
    rw [← terminal_physical_modelBand_eq_preimage]
    exact hRufix.mono subset_union_left
  obtain ⟨L, hL, R, hRfix, hRband, hRcap⟩ :=
    exists_simultaneous_terminal_replacement_of_side_replacements data E Rl Ru hEheight
      hKl hKu hRl hRu hlc.le hcu.le (hRlfix.mono subset_union_right)
      (hRufix.mono subset_union_right) hRlband hRuband hRlcap hRucap
  exact exists_simultaneous_flat_terminal_replacement_of_prepared data H E F R hK hL
    hFfix hFband hFcap hRfix hRband hRcap

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
