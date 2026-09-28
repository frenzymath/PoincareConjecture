import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.MovingNeighborhood







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
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_terminal_coordinate_model_transport
    (d : TerminalSaddleGeometry M P p e) (s : ActualStripData d)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hsize : 2 * d.r < Real.sqrt d.scale * d.matchingRadius)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hQi : ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2))
    {a ε : Real} (hε : 0 < ε) (hmargin : 8 * d.r < a)
    (hpatch : ∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
      Q t x = Saddle.toE2 (d.flatten (g (e x)))) :
    let c := inner Real (M.v : E3) (g p)
    ∃ (δ : Real) (C K O N : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ ε ∧ δ ≤ d.delta ∧ δ < d.eta ∧
      IsCompact C ∧ C ⊆ Q 0 '' openSquare (2 * d.r) ∧ IsCompact K ∧ IsOpen O ∧
      C ⊆ O ∧ Disjoint K O ∧ IsOpen N ∧ C ⊆ N ∧
      N ⊆ Q 0 '' openSquare (2 * d.r) ∧ IsOpen V ∧
      (d.flatten ∘ g) '' (e '' closedSquare d.r) ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        {x : E2 | Saddle.toE3 x (c + t) ∈
          (d.flatten ∘ g) '' (e '' closedSquare d.r)} ⊆ C) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ x, Saddle.toE3 x (c + t) ∈ V → x ∈ C) ∧
      (∀ t ∈ Icc (-δ) δ, d.A (c + t) \ C = d.A c \ C) ∧
      (∀ t ∈ Icc (-δ) δ, d.A (c + t) ∩ N = d.B (c + t) ∩ N) ∧
      (∀ t ∈ Icc (-δ) δ, C ⊆ Q t '' openSquare (4 * d.r)) ∧
      ∃ Psi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Psi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Psi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Psi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Psi t x = x) ∧
        (∀ t x, x ∈ O → Psi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ, Psi t '' (d.B c \ C) = d.B (c + t) \ C := by
  dsimp only
  let Nreg := Q 0 '' openSquare (2 * d.r)
  have hNreg : IsOpen Nreg := (Q 0).toHomeomorph.isOpenMap _ (isOpen_openSquare _)
  have hra : d.r < a := by linarith [d.r_pos]
  have hQNreg : Saddle.toE2 '' (((d.flatten ∘ g) '' (e '' closedSquare d.r)) ∩
      {y : E3 | y 2 = inner Real (M.v : E3) (g p)}) ⊆ Nreg := by
    rintro _ ⟨y, ⟨⟨q, ⟨x, hx, rfl⟩, rfl⟩, hz⟩, rfl⟩
    have hxt : -x 0 ^ 2 + x 1 ^ 2 = 0 := by
      change d.frame (d.D (g (e x))) 2 = _ at hz
      rw [d.frame_height, d.D_height, hform x (d.square_source hx)] at hz
      linarith
    refine ⟨x, ?_, hpatch 0 x ⟨hx.1.trans hra.le, hx.2.trans hra.le⟩ hxt⟩
    exact ⟨hx.1.trans_lt (by linarith [d.r_pos]), hx.2.trans_lt (by linarith [d.r_pos])⟩
  obtain ⟨δ₀, C, K, O, N, V, hδ₀, hδ₀d, hC, hCNreg, hK, hO, hCO, hKO,
      hN, hCN, hNNreg, hV, hpatchV, hpatchC, hfibers, hstationary, hcommon,
      Psi, hPsi0, hPsi, hPsii, hPsifix, hPsiO, htransport⟩ :=
    exists_terminal_model_slab_transport d s hg hsize hform Nreg hNreg hQNreg
  have hCinside : C ⊆ Q 0 '' openSquare (4 * d.r) := by
    apply hCNreg.trans
    apply image_mono
    intro x hx
    exact ⟨hx.1.trans (by linarith [d.r_pos]), hx.2.trans (by linarith [d.r_pos])⟩
  obtain ⟨δQ, hδQ, hinside⟩ := exists_uniform_compact_subset_moving_image Q hQi.continuous
    hC (isOpen_openSquare _) hCinside
  let δ := min ε (min δ₀ (min δQ (d.eta / 2)))
  have hδ : 0 < δ := lt_min hε (lt_min hδ₀ (lt_min hδQ (half_pos d.eta_pos)))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ₀bound : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδQbound : δ ≤ δQ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδη : δ < d.eta :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans_lt
      (half_lt_self d.eta_pos)
  have htime {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-δ₀) δ₀ :=
    ⟨by linarith [ht.1], ht.2.trans hδ₀bound⟩
  refine ⟨δ, C, K, O, N, V, hδ, hδε, hδ₀bound.trans hδ₀d, hδη,
    hC, hCNreg, hK, hO, hCO, hKO, hN, hCN, hNNreg, hV, hpatchV,
    (fun t ht => hpatchC t (htime ht)), (fun t ht => hfibers t (htime ht)),
    (fun t ht => hstationary t (htime ht)), (fun t ht => hcommon t (htime ht)),
    (fun t ht => hinside t ((abs_le.mpr ht).trans hδQbound)),
    Psi, hPsi0, hPsi, hPsii, hPsifix, hPsiO, fun t ht => htransport t (htime ht)⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
