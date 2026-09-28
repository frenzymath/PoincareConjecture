import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Simultaneous

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem saddle_cap_replacement_leaf
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    {P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (K : Set E2) (χ : Real → Real)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (_hK : IsCompact K)
    (_hfix : ∀ t z x, x ∉ K → Φ t z x = x)
    (hχ : ContDiff Real ∞ χ)
    (hχone : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∀ H₁ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, H₁ y = planarHeightMap Φ (χ (y 2)) y) →
      ∃ H₂ : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        EqOn H₂ id data.toTerminalSaddleGeometry.modelBand ∧
        ∀ i, H₂ '' (H₁ '' data.toTerminalSaddleGeometry.C i) =
          data.toTerminalSaddleGeometry.modelCaps i := by
  intro H₁ hH₁
  obtain ⟨_, _, H₂, _, hband, hcaps⟩ :=
    Saddle.Caps.Closing.exists_supported_terminal_curved_collar_transport data hg Φ hzero hΦ
      hΦinv χ hχ H₁ hH₁ hχone hplanar hlabels
  exact ⟨H₂, hband, hcaps⟩
end Poincare.Manifold.Schoenflies.SaddleLevel

end

end M38Schoenflies
