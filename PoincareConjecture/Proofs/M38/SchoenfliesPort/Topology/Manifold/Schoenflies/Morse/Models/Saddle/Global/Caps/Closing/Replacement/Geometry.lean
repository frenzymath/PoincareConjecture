import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Sides

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_physical_modelBand_eq_preimage (data : TerminalSaddleData M P p e) :
    data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelBand =
      data.toTerminalSaddleGeometry.flatten ⁻¹' data.toTerminalSaddleGeometry.modelBand := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_preimage, Diffeomorph.apply_symm_apply] using hx
  · intro hy
    exact ⟨data.toTerminalSaddleGeometry.flatten y, hy,
      data.toTerminalSaddleGeometry.flatten.symm_apply_apply y⟩

theorem isClosed_terminal_physical_modelBand (data : TerminalSaddleData M P p e) :
    IsClosed (data.toTerminalSaddleGeometry.flatten.symm ''
      data.toTerminalSaddleGeometry.modelBand) :=
  ((isCompact_terminal_modelBand data).image
    data.toTerminalSaddleGeometry.flatten.symm.continuous).isClosed

theorem terminal_physical_modelCap_eq_image (data : TerminalSaddleData M P p e) (i : Fin 3) :
    data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelCaps i =
      (fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
        data.toTerminalSaddleGeometry.modelDomain i := by
  unfold TerminalSaddleGeometry.modelCaps
  rw [image_image]
  simp only [Diffeomorph.symm_apply_apply]

theorem terminal_prepared_caps_disjoint (data : TerminalSaddleData M P p e)
    (E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    Pairwise (fun i j : Fin 3 => Disjoint
      ((E ∘ g) '' terminalEndCap data.ends (data.labels i))
      ((E ∘ g) '' terminalEndCap data.ends (data.labels j))) := by
  intro i j hij
  have hd := data.actual_disjoint hij
  change Disjoint ((data.toTerminalSaddleGeometry.flatten ∘ g) '' _)
    ((data.toTerminalSaddleGeometry.flatten ∘ g) '' _) at hd
  apply disjoint_left.mpr
  rintro y ⟨q, hq, hqy⟩ ⟨r, hr, hry⟩
  have heq : g q = g r := E.injective (hqy.trans hry.symm)
  exact disjoint_left.mp hd ⟨q, hq, rfl⟩
    ⟨r, hr, congrArg data.toTerminalSaddleGeometry.flatten heq.symm⟩

theorem terminal_physical_modelCaps_disjoint (data : TerminalSaddleData M P p e) :
    Pairwise (fun i j : Fin 3 => Disjoint
      ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
        data.toTerminalSaddleGeometry.modelDomain i)
      ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
        data.toTerminalSaddleGeometry.modelDomain j)) := by
  intro i j hij
  rw [← terminal_physical_modelCap_eq_image, ← terminal_physical_modelCap_eq_image]
  exact (disjoint_image_iff data.toTerminalSaddleGeometry.flatten.symm.injective).mpr
    (data.model_disjoint hij)

theorem terminal_lower_model_domain_height (data : TerminalSaddleData M P p e) (i : Fin 3)
    (hseed : inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel (data.modelSeed i)) < data.ends.lowerCut)
    {q : S2} (hq : q ∈ data.toTerminalSaddleGeometry.modelDomain i) :
    inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) ≤ data.ends.lowerCut := by
  rcases terminal_model_domain_component data i with ⟨_, heq⟩ | ⟨hh, _⟩
  · rw [heq] at hq
    exact connectedComponentIn_subset
      ((fun q : S2 => inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q)) ⁻¹'
        Iic data.ends.lowerCut) (data.modelSeed i) hq
  · exact ((hseed.trans data.ends.cuts_lt).not_gt hh).elim

theorem terminal_upper_model_domain_height (data : TerminalSaddleData M P p e) (i : Fin 3)
    (hseed : data.ends.upperCut < inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel (data.modelSeed i)))
    {q : S2} (hq : q ∈ data.toTerminalSaddleGeometry.modelDomain i) :
    data.ends.upperCut ≤ inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) := by
  rcases terminal_model_domain_component data i with ⟨hh, _⟩ | ⟨_, heq⟩
  · exact ((hh.trans data.ends.cuts_lt).not_gt hseed).elim
  · rw [heq] at hq
    exact connectedComponentIn_subset
      ((fun q : S2 => inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q)) ⁻¹'
        Ici data.ends.upperCut) (data.modelSeed i) hq

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
