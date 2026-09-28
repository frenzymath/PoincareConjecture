import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Surface
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Perturbation.Isotopy
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Chart



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev P := E2 × Real



theorem exists_ambient_height_shift_in_coordinates
    (F : OpenPartialHomeomorph P E3)
    (hF : ContDiffOn Real ∞ F F.source)
    (hFi : ContDiffOn Real ∞ F.symm F.target)
    (v : E3) {h : E2 -> Real} (hh : ContDiff Real ∞ h)
    (hheight : ∀ z ∈ F.source, inner Real v (F z) = h z.1 + z.2)
    {r R S ε : Real} (hr : 0 < r) (hrR : r < R) (hS : 0 < S) (hε : 0 < ε)
    (hcylinder : closedBall (0 : E2) R ×ˢ closedBall (0 : Real) S ⊆ F.source)
    (hregular : ∀ x ∈ closedBall (0 : E2) R \ ball 0 r, fderiv Real h x ≠ 0)
    {A : Set Real} (hA : A.Finite) :
    ∃ (K : Set E3) (b : E2 -> Real) (a : Real)
        (Phi : Real -> Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      IsCompact K ∧ K ⊆ F.target ∧ ContDiff Real ∞ b ∧
      tsupport b ⊆ closedBall 0 R ∧ EqOn b 1 (closedBall 0 r) ∧
      |a| < ε ∧ h 0 + a ∉ A ∧
      (∀ y, Phi 0 y = y) ∧
      ContDiff Real ∞ (fun z : Real × E3 => Phi z.1 z.2) ∧
      (∀ s y, y ∉ K -> Phi s y = y) ∧
      (∀ s x, (x, 0) ∈ F.source ->
        Phi s (F (x, 0)) = F (x, Real.smoothTransition s * a * b x)) ∧
      (∀ s x, (x, 0) ∈ F.source ->
        inner Real v (Phi s (F (x, 0))) = h x + Real.smoothTransition s * a * b x) ∧
      ∀ s x, fderiv Real (fun y => h y + (Real.smoothTransition s * a) * b y) x = 0 ↔
        fderiv Real h x = 0 := by
  obtain ⟨b, a, G, hb, hbR, hbone, ha, hG0, hGs, hGfix, hGzero, hcritical, havoid⟩ :=
    exists_supported_zero_section_height_shift hh 0 hr hrR hS hε hregular hA
  let L := closedBall (0 : E2) R ×ˢ closedBall (0 : Real) S
  have hL : IsCompact L := (isCompact_closedBall 0 R).prod (isCompact_closedBall 0 S)
  obtain ⟨hK, hKt, Phi, hPhi0, hPhis, hPhifix, hPhicoord⟩ :=
    exists_supported_chart_isotopy F hF.contMDiffOn hFi.contMDiffOn hL hcylinder
      G hG0 hGs hGfix
  have hmaps (s : Real) : MapsTo (G s) F.source F.source := by
    intro z hz
    by_contra hout
    have hnot : G s z ∉ L := fun ht => hout (hcylinder ht)
    have heq : G s z = z := (G s).injective (hGfix s (G s z) hnot)
    exact hout (heq.symm ▸ hz)
  refine ⟨F '' L, b, a, Phi, hK, hKt, hb, hbR, hbone, ha, havoid,
    hPhi0, ?_, hPhifix, ?_, ?_, hcritical⟩
  · rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hPhis
    exact hPhis.contDiff
  · intro s x hx
    rw [hPhicoord s _ hx, hGzero]
  · intro s x hx
    rw [hPhicoord s _ hx, hheight _ (hmaps s hx), hGzero]

end Poincare.Manifold.Schoenflies
