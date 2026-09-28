import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.TerminalData
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Leaves

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

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def TerminalSaddleGeometry.toAccepted
    {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
    {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (d : OrientationReview.TerminalSaddleGeometry M P p e)
    (hk : d.model = Saddle.shear ∨ d.model = Saddle.Nested.shear (3/10)) :
    SaddleLevel.TerminalSaddleGeometry M P p e :=
  { D := d.D
    frame := d.frame
    frame_height := d.frame_height
    frame_isometry := d.frame_isometry
    frame_zero := d.frame_zero
    r := d.r
    delta := d.delta
    r_pos := d.r_pos
    square_source := d.square_source
    delta_pos := d.delta_pos
    delta_lt := d.delta_lt
    D_height := d.D_height
    strips := d.strips
    a := d.a
    b := d.b
    leftContact := d.leftContact
    rightContact := d.rightContact
    flattened_levels := d.flattened_levels
    model := d.model
    model_kind := hk
    transport := d.transport
    scale := d.scale
    scale_pos := d.scale_pos
    modelChart := d.modelChart
    modelChart_zero := d.modelChart_zero
    modelChart_smooth := d.modelChart_smooth
    modelChart_symm_smooth := d.modelChart_symm_smooth
    matchingRadius := d.matchingRadius
    matchingRadius_pos := d.matchingRadius_pos
    matching_source := d.matching_source
    matching_actual_source := d.matching_actual_source
    transport_height := d.transport_height
    matching := d.matching
    ends := d.ends
    eta := d.eta
    eta_pos := d.eta_pos
    eta_lt := d.eta_lt
    lowerCut_eq := d.lowerCut_eq
    upperCut_eq := d.upperCut_eq
    labels := d.labels
    modelSeed := d.modelSeed
    modelSeed_outside := d.modelSeed_outside }

def TerminalSaddleData.toAccepted
    {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
    {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (d : OrientationReview.TerminalSaddleData M P p e)
    (hk : d.toTerminalSaddleGeometry.model = Saddle.shear ∨
      d.toTerminalSaddleGeometry.model = Saddle.Nested.shear (3/10)) :
    SaddleLevel.TerminalSaddleData M P p e :=
  { toTerminalSaddleGeometry := d.toTerminalSaddleGeometry.toAccepted hk
    actualDisk := d.actualDisk
    actualDisk_source := d.actualDisk_source
    actualDisk_smooth := d.actualDisk_smooth
    actualDisk_symm_smooth := d.actualDisk_symm_smooth
    actualDisk_image := d.actualDisk_image
    modelDisk := d.modelDisk
    modelDisk_source := d.modelDisk_source
    modelDisk_smooth := d.modelDisk_smooth
    modelDisk_symm_smooth := d.modelDisk_symm_smooth
    modelDisk_image := d.modelDisk_image
    actual_decomposition := d.actual_decomposition
    model_decomposition := d.model_decomposition
    actual_boundary := d.actual_boundary
    model_boundary := d.model_boundary
    actual_disjoint := d.actual_disjoint
    model_disjoint := d.model_disjoint }

theorem saddle_cap_replacement_original
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    {P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g}
    {p : S2} {e : OpenPartialHomeomorph E2 S2}
    (data : OrientationReview.TerminalSaddleData M P p e)
    (hk : data.toTerminalSaddleGeometry.model = Saddle.shear ∨
      data.toTerminalSaddleGeometry.model = Saddle.Nested.shear (3/10))
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (K : Set E2) (χ : Real → Real)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (hK : IsCompact K)
    (hfix : ∀ t z x, x ∉ K → Φ t z x = x)
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
  obtain ⟨H₂, hband, hcaps⟩ :=
    SaddleLevel.saddle_cap_replacement_leaf M hg (data.toAccepted hk) Φ K χ hzero hΦ hΦinv hK
      hfix hχ hχone hplanar hlabels H₁ hH₁
  exact ⟨H₂, hband, hcaps⟩

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview

end

end M38Schoenflies
