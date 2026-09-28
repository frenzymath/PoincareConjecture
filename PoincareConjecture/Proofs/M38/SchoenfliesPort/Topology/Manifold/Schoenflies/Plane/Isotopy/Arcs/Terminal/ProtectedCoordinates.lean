import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.MovingCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.MovingNeighborhood
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.StationarySlices

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_terminal_geometry_with_protected_morse_coordinates
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∀ nested : Bool, ∃ d : TerminalSaddleGeometry M P p e,
      d.model = (if nested then Saddle.Nested.shear (3 / 10) else Saddle.shear) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius ∧
      ∃ a δ : Real, 0 < a ∧ 0 < δ ∧ 8 * d.r < a ∧ δ ≤ d.delta ∧ δ < d.eta ∧
        closedSquare a ⊆ e.source ∧
        ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧
          ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
            ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
            ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
            (∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
              Q t x = Saddle.toE2 (d.flatten (g (e x)))) ∧
            (∀ x ∈ closedSquare a, ∀ t ∈ Icc (-δ) δ,
              (Q t x ∈ d.A (inner Real (M.v : E3) (g p) + t) ↔
                -x 0 ^ 2 + x 1 ^ 2 = t) ∧
              (Q t x ∈ d.B (inner Real (M.v : E3) (g p) + t) ↔
                -x 0 ^ 2 + x 1 ^ 2 = t)) ∧
            (∀ t ∈ Icc (-δ) δ, closure N ⊆ Q t '' openSquare (4 * d.r)) ∧
            (∀ t ∈ Icc (-δ) δ,
              d.A (inner Real (M.v : E3) (g p) + t) ∩ closure N =
                d.B (inner Real (M.v : E3) (g p) + t) ∩ closure N) ∧
            (∀ t ∈ Icc (-δ) δ,
              d.A (inner Real (M.v : E3) (g p) + t) \ closure N =
                d.A (inner Real (M.v : E3) (g p)) \ closure N) ∧
            ∀ t ∈ Icc (-δ) δ, ∀ x ∈ closedSquare d.r,
              -x 0 ^ 2 + x 1 ^ 2 = t → Saddle.toE2 (d.flatten (g (e x))) ∈ N := by
  intro nested
  obtain ⟨d, hmodel, _, hsize, a, ε, ha, hε, hmargin, hsource, Q, hQ, hQi,
      hpatch, hslice⟩ := exists_terminal_geometry_with_matched_moving_morse_coordinates M hg P
        hP hcaps hp hc hunique he0 hep he hei het hform nested
  have hra : d.r < a := by linarith [d.r_pos]
  have hrsource : closedSquare d.r ⊆ closedSquare a :=
    fun x hx => ⟨hx.1.trans hra.le, hx.2.trans hra.le⟩
  let V := Q 0 '' openSquare (2 * d.r)
  have hV : IsOpen V := (Q 0).toHomeomorph.isOpenMap _ (isOpen_openSquare _)
  have hcritical (x : E2) (hx : x ∈ closedSquare d.r)
      (hz : (d.flatten (g (e x))) 2 = inner Real (M.v : E3) (g p)) :
      Saddle.toE2 (d.flatten (g (e x))) ∈ V := by
    have hxt : -x 0 ^ 2 + x 1 ^ 2 = 0 := by
      change d.frame (d.D (g (e x))) 2 = _ at hz
      rw [d.frame_height, d.D_height, hform x (d.square_source hx)] at hz
      linarith
    refine ⟨x, ?_, hpatch 0 x (hrsource hx) hxt⟩
    exact ⟨hx.1.trans_lt (by linarith [d.r_pos]), hx.2.trans_lt (by linarith [d.r_pos])⟩
  obtain ⟨εN, hεN, hεNd, N, hN, hNc, hNV, hcommon, hstationary, hprotected⟩ :=
    exists_terminal_stationary_exterior_neighborhood_within hg d hsize hform V hV hcritical
  have hNinside : closure N ⊆ Q 0 '' openSquare (4 * d.r) := by
    apply hNV.trans
    apply image_mono
    intro x hx
    exact ⟨hx.1.trans (by linarith [d.r_pos]), hx.2.trans (by linarith [d.r_pos])⟩
  obtain ⟨εQ, hεQ, hinside⟩ := exists_uniform_compact_subset_moving_image Q hQi.continuous
    hNc (isOpen_openSquare _) hNinside
  let δ := min ε (min εN (min εQ (d.eta / 2)))
  have hδ : 0 < δ := lt_min hε (lt_min hεN (lt_min hεQ (half_pos d.eta_pos)))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδN : δ ≤ εN := (min_le_right _ _).trans (min_le_left _ _)
  have hδQ : δ ≤ εQ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδη : δ < d.eta :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans_lt
      (half_lt_self d.eta_pos)
  have htime {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-εN) εN :=
    ⟨by linarith [ht.1], ht.2.trans hδN⟩
  refine ⟨d, hmodel, hsize, a, δ, ha, hδ, hmargin, hδN.trans hεNd, hδη, hsource,
    N, hN, hNc, Q, hQ, hQi, hpatch, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx t ht
    exact hslice x hx t ⟨by linarith [ht.1], ht.2.trans hδε⟩
  · intro t ht
    exact hinside t ((abs_le.mpr ht).trans hδQ)
  · intro t ht
    exact hcommon t (htime ht)
  · intro t ht
    exact hstationary t (htime ht)
  · intro t ht
    exact hprotected t (htime ht)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
