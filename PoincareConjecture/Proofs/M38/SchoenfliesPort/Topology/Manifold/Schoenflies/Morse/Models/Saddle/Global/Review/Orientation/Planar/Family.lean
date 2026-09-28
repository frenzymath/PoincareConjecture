import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Inclusion
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Selection
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Transport
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Data
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Ends

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar
open PlaneArcs.Terminal.Reflection Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def FourModelPlanarFamily {f : S2 → E3} {p : S2} (s : TerminalInputData f p) : Prop :=
  ∃ data : TerminalSaddleData s.reduction s.path p s.chart,
    let d := data.toTerminalSaddleGeometry
    ∃ (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
      (K : Set E2) (χ : Real → Real),
      (∀ z x, Φ 0 z x = x) ∧
      ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2) ∧
      ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2) ∧
      IsCompact K ∧ (∀ u z x, x ∉ K → Φ u z x = x) ∧
      ContDiff Real ∞ χ ∧ (∀ z ∈ d.I, χ z = 1) ∧
      (∀ z ∈ d.I, Φ 1 z '' d.A z = d.B z) ∧
      (∀ i, planarHeightMap Φ 1 '' (d.C i ∩ d.actualBand) =
        d.modelCaps i ∩ d.modelBand) ∧
      ∃ ρ > 0, ∃ U : Set E3, IsOpen U ∧ closedSquare ρ ⊆ s.chart.source ∧
        (∀ x ∈ closedSquare ρ,
          (Real.sqrt d.scale)⁻¹ • x ∈ closedBall (0 : E2) d.matchingRadius) ∧
        (d.flatten ∘ s.leaf ∘ s.chart) '' closedSquare ρ ⊆ U ∧
        ∀ u, EqOn (planarHeightMap Φ u) id U

private theorem include_fullPlanarFamily
    {f : S2 → E3} {p : S2} (s : TerminalInputData f p)
    (h : FullPlanarFamily s) : FourModelPlanarFamily s := by
  obtain ⟨data, Φ, K, χ, hfamily⟩ := h
  exact ⟨includeData data, Φ, K, χ, hfamily⟩

theorem exists_four_model_planar_family
    {f : S2 → E3} {p : S2} (s : TerminalInputData f p) : FourModelPlanarFamily s := by
  rcases exists_original_or_reflected_planar_family s with hfamily | hfamily
  · exact include_fullPlanarFamily s hfamily
  obtain ⟨s', hv, _, hg, hcore, he, hinit, data, Φ, K, χ,
    hzero, hΦ, hΦinv, hK, hfix, hχ, hχone, hplanar, hlabels,
    ρ, hρ, U, hU, hsource, hmodel, hpatch, hprotected⟩ := hfamily
  let d := data.toTerminalSaddleGeometry
  obtain ⟨A, hl, hu, L, hcaps⟩ := exists_original_ends s s' hv hg hcore hinit d
  let data' := reflectData s s' hv hg he data A hl hu L hcaps
  let G := reflectGeometry s s' hv hg he d A hl hu L
  have hGI (z : Real) : z ∈ G.I ↔ -z ∈ d.I :=
    reflectGeometry_mem_I s s' hv hg he d A hl hu L z
  refine ⟨data', reflectedPlanarFamily Φ, K, (fun z => χ (-z)),
    (fun z x => hzero (-z) x), reflectedPlanarFamily_smooth Φ hΦ,
    reflectedPlanarFamily_inverse_smooth Φ hΦinv, hK,
    (fun u z x hx => hfix u (-z) x hx), hχ.comp contDiff_neg,
    (fun z hz => hχone (-z) ((hGI z).mp hz)), ?_, ?_,
    ρ, hρ, Rz '' U, Rz.toHomeomorph.isOpenMap U hU, ?_, ?_, ?_,
    reflectedPlanarHeightMap_fixed Φ hprotected⟩
  · intro z hz
    change Φ 1 (-z) '' G.A z = G.B z
    rw [reflectGeometry_A s s' hv hg he d A hl hu L,
      reflectGeometry_B s s' hv hg he d A hl hu L]
    exact hplanar (-z) ((hGI z).mp hz)
  · intro i
    change planarHeightMap (reflectedPlanarFamily Φ) 1 '' (G.C i ∩ G.actualBand) =
      G.modelCaps i ∩ G.modelBand
    rw [reflectGeometry_C s s' hv hg he d A hl hu L hcaps,
      reflectGeometry_actualBand s s' hv hg he d A hl hu L,
      reflectGeometry_modelCaps s s' hv hg he d A hl hu L,
      reflectGeometry_modelBand s s' hv hg he d A hl hu L,
      ← Rz_image_inter, reflectedPlanarHeightMap_image]
    change Rz '' (SaddleLevel.planarHeightMap Φ 1 '' (d.C i ∩ d.actualBand)) = _
    rw [hlabels i, Rz_image_inter]
  · apply square_source_reflection
    rw [← he]
    exact hsource
  · exact hmodel
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨d.flatten (s'.leaf (s'.chart (swapPlanarCoordinates x))),
      hpatch ⟨swapPlanarCoordinates x,
        (swapPlanarCoordinates_mem_closedSquare x ρ).mpr hx, rfl⟩, ?_⟩
    change Rz (d.flatten (s'.leaf (s'.chart (swapPlanarCoordinates x)))) =
      G.flatten (s.leaf (s.chart x))
    rw [reflectGeometry_flatten_leaf s s' hv hg he d A hl hu L]
    apply congrArg (fun q => Rz (d.flatten (s'.leaf q)))
    rw [he]
    change s.chart (swapPlanarCoordinates (swapPlanarCoordinates x)) = s.chart x
    rw [swapPlanarCoordinates_involutive]

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar

end

end M38Schoenflies
