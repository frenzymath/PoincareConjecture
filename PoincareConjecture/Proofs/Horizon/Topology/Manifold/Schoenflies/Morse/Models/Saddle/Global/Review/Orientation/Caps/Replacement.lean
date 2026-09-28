import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.Conjugation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.ReflectedData







noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem saddle_cap_replacement
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
  have cases := data.model_kind
  rcases cases with hk | hk | hk
  · exact saddle_cap_replacement_original M hg data (Or.inl hk) Φ K χ hzero hΦ hΦinv
      hK hfix hχ hχone hplanar hlabels
  · exact saddle_cap_replacement_original M hg data (Or.inr hk) Φ K χ hzero hΦ hΦinv
      hK hfix hχ hχone hplanar hlabels
  intro H₁ hH₁
  obtain ⟨R, hv, _, _, hinit, hleaves⟩ := M.exists_reflected
  obtain ⟨Q, hcore⟩ := exists_reflected_path M P R hv hinit
  obtain ⟨data', hI, hA, hB, hC, hmodelCaps, hactualBand, hmodelBand⟩ :=
    exists_reflectedData M P (p := p) (e := e) data hk R hv Q hcore hinit
  have hplanar' : ∀ z ∈ data'.toTerminalSaddleGeometry.I,
      reflectedPlanarFamily Φ 1 z '' data'.toTerminalSaddleGeometry.A z =
        data'.toTerminalSaddleGeometry.B z := by
    intro z hz
    rw [hA, hB]
    exact hplanar (-z) ((hI z).mp hz)
  have hlabels' : ∀ i, SaddleLevel.planarHeightMap (reflectedPlanarFamily Φ) 1 ''
      (data'.toTerminalSaddleGeometry.C i ∩ data'.toTerminalSaddleGeometry.actualBand) =
      data'.toTerminalSaddleGeometry.modelCaps i ∩ data'.toTerminalSaddleGeometry.modelBand := by
    intro i
    rw [hC, hactualBand, hmodelCaps, hmodelBand, ← Rz_image_inter]
    change planarHeightMap (reflectedPlanarFamily Φ) 1 ''
      (Rz '' (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand)) = _
    rw [reflectedPlanarHeightMap_image, hlabels, Rz_image_inter]
  obtain ⟨F, hFfix, hFcap⟩ := SaddleLevel.saddle_cap_replacement_leaf R (hleaves g hg)
    data' (reflectedPlanarFamily Φ) K (fun z => χ (-z))
    (fun z x => hzero (-z) x) (reflectedPlanarFamily_smooth Φ hΦ)
    (reflectedPlanarFamily_inverse_smooth Φ hΦinv) hK
    (fun t z x hx => hfix t (-z) x hx) (hχ.comp contDiff_neg)
    (fun z hz => hχone (-z) ((hI z).mp hz)) hplanar' hlabels'
    ((Rz.trans H₁).trans Rz) (reflected_lift Φ χ H₁ hH₁)
  apply conjugate_replacement H₁ F data.toTerminalSaddleGeometry.C
    data.toTerminalSaddleGeometry.modelCaps data.toTerminalSaddleGeometry.modelBand
  · rwa [hmodelBand] at hFfix
  · intro i
    simpa only [hC, hmodelCaps] using hFcap i

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps
