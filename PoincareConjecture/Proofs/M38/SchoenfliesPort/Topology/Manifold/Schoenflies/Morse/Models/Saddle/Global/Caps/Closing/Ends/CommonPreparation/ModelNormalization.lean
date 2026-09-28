import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.TerminalAnnulus
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Normalization
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.AxisReversal







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
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel Poincare.Geometry.Euclidean _root_.Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_buffered_terminal_model_normalization_with_common_preparation
    (data : TerminalSaddleData M P p e) (i : Fin 3)
    {v : E3} (hv : ‖v‖ = 1) {b : Real}
    (hside : (v = (M.v : E3) ∧ b = data.ends.lowerCut) ∨
      (v = -(M.v : E3) ∧ b = -data.ends.upperCut))
    (hboundary : ∀ x ∈ sphere (0 : E2) 1,
      inner Real v (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) = b)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQheight : ∀ y, inner Real v (Q y) = inner Real v y)
    (hQcompact : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Q y = y)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      Q (data.toTerminalSaddleGeometry.filledModel (T (q, t))) =
        (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = data.modelDisk i '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ data.modelDisk i '' ball 0 1) :
    ∃ l s : Real, ∃ hs : s < 0, l < b ∧
      ∃ B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v),
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
        (∃ τ : Real, 0 < τ ∧ ∀ y, b - τ ≤ inner Real v y → F y = Q y) ∧
        B '' sphere (0 : Hemisphere.Plane v) 1 = range γ ∧
        F '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
          data.toTerminalSaddleGeometry.modelDomain i) =
          (liftPlaneDiffeomorph hv l s hs.ne B '' boundedCylinderNorthernCap v) ∪
            terminalCylinder (range γ) l b := by
  let m : S2 → E3 := fun q => data.toTerminalSaddleGeometry.filledModel q
  let m' : S2 → E3 := Q ∘ m
  obtain ⟨h, b₀, q, C, horient, hh, hq, hqb, hB, hunique, hcomponent,
    hregular, hC0, hCq, hC, hCi, hform⟩ := exists_terminal_model_oriented_morse_cap data i
  let x : E2 := EuclideanSpace.single 0 1
  have hx : x ∈ sphere (0 : E2) 1 := by simp [x]
  have hcuts := data.ends.cuts_lt
  have halign : b₀ = b ∧ h = (fun z => inner Real v (m z)) := by
    rcases hside with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · have hb₁ := hB x hx
        have hb₂ := hboundary x hx
        simp only [Pi.neg_apply] at hb₁
        linarith
    · rcases horient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hb₁ := hB x hx
        have hb₂ := hboundary x hx
        rw [inner_neg_left] at hb₂
        dsimp only at hb₁
        linarith
      · refine ⟨rfl, ?_⟩
        funext z
        exact (inner_neg_left (M.v : E3) (m z)).symm
  obtain ⟨hb, hhphysical⟩ := halign
  subst b₀
  have hprepared : h = (fun z => inner Real v (m' z)) := by
    rw [hhphysical]
    funext z
    exact (hQheight (m z)).symm
  have hm' : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ m' := by
    let J := data.toTerminalSaddleGeometry.filledModel.trans Q
    have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q : S2 => (q : E3)) := contMDiff_coe_sphere
    apply isSmoothEmbedding_of_injective_mfderiv (J.contMDiff.comp hcoe)
      (J.injective.comp Subtype.val_injective)
    intro z
    change Injective (mfderiv (𝓡 2) (𝓡 3) (J ∘ (fun q : S2 => (q : E3))) z)
    rw [mfderiv_comp z (J.contMDiff.mdifferentiable (by simp) _)
      (hcoe.mdifferentiable (by simp) z)]
    exact (J.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (by convert! injective_mvfderiv_subtypeVal_sphere z)
  rw [hprepared] at hqb hunique hcomponent hregular hform
  have hB' : ∀ x ∈ sphere (0 : E2) 1, inner Real v (m' (data.modelDisk i x)) = b := by
    intro x hx
    exact (hQheight _).trans (hboundary x hx)
  obtain ⟨l, s, hs, hl, B, K, hK, N, hBcircle, hNfix, ⟨τ, hτ, hNhalf⟩, hNimage⟩ :=
    exists_buffered_relative_component_minimum_disk_normalization hm' hv (data.modelDisk i)
      (data.modelDisk_source i) hq hqb hB' hunique (data.modelSeed i) hcomponent
      hregular C hC0 hCq hC hCi hform hε T hTs γ hTcylinder hTc hTneg
  obtain ⟨KQ, hKQ, hQfix⟩ := hQcompact
  refine ⟨l, s, hs, hl, B, Q.trans N, ⟨KQ ∪ K, hKQ.union hK, ?_⟩, ?_, hBcircle, ?_⟩
  · intro y hy
    change N (Q y) = y
    rw [hQfix y (fun hh => hy (Or.inl hh)), hNfix y (fun hh => hy (Or.inr hh))]
  · refine ⟨τ, hτ, ?_⟩
    intro y hy
    change N (Q y) = Q y
    exact hNhalf _ (by rw [hQheight]; exact hy)
  · rw [← data.modelDisk_image i]
    change (N ∘ Q) '' (m '' _) = _
    rw [terminalCylinder_eq_height_product]
    simpa only [m', image_image, Function.comp_apply] using hNimage


theorem exists_terminal_model_normalization_with_common_preparation
    (data : TerminalSaddleData M P p e) (i : Fin 3)
    {v : E3} (hv : ‖v‖ = 1) {b : Real}
    (hside : (v = (M.v : E3) ∧ b = data.ends.lowerCut) ∨
      (v = -(M.v : E3) ∧ b = -data.ends.upperCut))
    (hboundary : ∀ x ∈ sphere (0 : E2) 1,
      inner Real v (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) = b)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQheight : ∀ y, inner Real v (Q y) = inner Real v y)
    (hQcompact : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Q y = y)
    {ε : Real} (hε : 0 < ε) (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hTs : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 → Hemisphere.Plane v)
    (hTcylinder : ∀ q t, t ∈ Ioo (-ε) ε →
      Q (data.toTerminalSaddleGeometry.filledModel (T (q, t))) =
        (b + t) • v + (γ q : E3))
    (hTc : range (fun q : S1 => T (q, 0)) = data.modelDisk i '' sphere (0 : E2) 1)
    (hTneg : ∀ q : S1, ∀ t ∈ Ioo (-ε) 0, T (q, t) ∈ data.modelDisk i '' ball 0 1) :
    ∃ l s : Real, ∃ hs : s < 0, l < b ∧
      ∃ B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v),
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
        (∀ y, b ≤ inner Real v y → F y = Q y) ∧
        B '' sphere (0 : Hemisphere.Plane v) 1 = range γ ∧
        F '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
          data.toTerminalSaddleGeometry.modelDomain i) =
          (liftPlaneDiffeomorph hv l s hs.ne B '' boundedCylinderNorthernCap v) ∪
            terminalCylinder (range γ) l b := by
  obtain ⟨l, s, hs, hl, B, F, hF, ⟨τ, hτ, hu⟩, hB, hi⟩ :=
    exists_buffered_terminal_model_normalization_with_common_preparation data i hv hside
      hboundary Q hQheight hQcompact hε T hTs γ hTcylinder hTc hTneg
  exact ⟨l, s, hs, hl, B, F, hF, fun y hy => hu y (by linarith), hB, hi⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
