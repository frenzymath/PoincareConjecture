import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.PairedOrientedCollars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.ComponentRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.OriginalPairedSourceAnnuli

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => (P2 × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}

structure PairedCircleCollars (D : OrdinaryIntervalMarkedModel old i) (L d : ℝ) where
  length_pos : 0 < L
  tube : C3 → X
  source : Fin 2 → Set V2
  collar : ∀ j, _root_.Dehn.OrientedPolygonCollar L d (source j)
  tube_PL : PolyhedralPLInCharts e tube (_root_.Dehn.identityTube L d)
  tube_interior : MapsTo tube (_root_.Dehn.identityTube L d) (interior R)
  tube_fibers : ∀ z ∈ _root_.Dehn.identityTube L d,
    ∀ w ∈ _root_.Dehn.identityTube L d,
      tube z = tube w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))
  source_clip : ∀ j, source j ⊆ (D.clips j.castSucc).space
  source_interior : ∀ j, source j ⊆ ball 0 1
  source_disjoint : Disjoint (source 0) (source 1)
  full_preimage : D2 ∩ f ⁻¹' (tube '' _root_.Dehn.identityTube L d) = source 0 ∪ source 1
  middle : ∀ j p, ((collar j).chart p : V2) ∈
    old.pieces (if j = 0 then i else old.mate i) ↔ depth L p = 0
  middle_image : ∀ j, (fun p ↦ ((collar j).chart p : V2)) '' {p | depth L p = 0} =
    old.pieces (if j = 0 then i else old.mate i)
  double_intersection : ∀ j, source j ∩ doubleLocusOn f D2 =
    old.pieces (if j = 0 then i else old.mate i)
  period_value : ∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L))
    (u : Icc (-d) d) (p : squareAnnulus L d),
      (p : P2) = annulusMap L length_pos ((s : AddCircle (4 * L)), u) →
      f ((collar j).chart p) = tube (sourceTubeDiagonal j u, s)

theorem OrdinaryIntervalMarkedModel.nonempty_paired_circle_collars
    (D : OrdinaryIntervalMarkedModel old i) (hcore : D.core ⊆ interior R)
    (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    {m : ℕ} (P : Polygon V2 (m + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i)
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    Nonempty (PairedCircleCollars D L d) := by
  classical
  let _ : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨N, sigma, tau, A, c, hsigma, hsigmaImage, hsigmaK, hsheet, haxis,
    hsigmaFib, htau, htauPL, htauInterior, htauFib, htauImage, htauSheet, htauClip,
    hc, hA, hdis, hvalue, hgraph, hmiddle, hmiddleImage, hpre⟩ :=
    D.exists_original_paired_source_annuli hcore P hP hPi hPs hd hwidth
  obtain ⟨B, tau', hPL, him, hfib, hcenter, hval⟩ :=
    _root_.Dehn.exists_paired_oriented_polygon_collars
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) e hd hwidth A c
      (fun j ↦ (hc j).1) f tau htauPL htauFib hvalue
  have hAI (j : Fin 2) : A j ⊆ ball 0 1 := by
    intro x hx
    have hxclip := hA j hx
    have hxs := ((D.clips_data j.castSucc).2.1.subset hxclip).1
    have hxf := ((D.clips_data j.castSucc).2.1.subset hxclip).2
    have hxD := D.source_subset j.castSucc hxs
    have hxnot : x ∉ Q2 := by
      intro hxQ
      exact disjoint_left.mp disjoint_interior_frontier (hcore hxf)
        ((hfront x hxD).mpr hxQ)
    rw [mem_ball, dist_zero_right]
    have hle : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hxD
    exact lt_of_le_of_ne hle (fun heq ↦ hxnot (by simpa [mem_sphere, dist_zero_right] using heq))
  have hm (j : Fin 2) (p : squareAnnulus L d) :
      ((B j).chart p : V2) ∈ old.pieces (if j = 0 then i else old.mate i) ↔
        depth L p = 0 := by
    have hh := hmiddle j ((c j).symm ((B j).chart p))
    rw [(c j).apply_symm_apply] at hh
    exact hh.trans (hcenter j p)
  have hmi (j : Fin 2) : (fun p ↦ ((B j).chart p : V2)) '' {p | depth L p = 0} =
      old.pieces (if j = 0 then i else old.mate i) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hm j p).mpr hp
    · intro hx
      have hxA : x ∈ A j := by
        obtain ⟨p, _, hp⟩ := (hmiddleImage j).symm.subset hx
        exact hp ▸ (c j p).property
      let p := (B j).chart.symm ⟨x, hxA⟩
      refine ⟨p, (hm j p).mp ?_, ?_⟩
      · simpa only [p, (B j).chart.apply_symm_apply] using hx
      · exact congrArg Subtype.val ((B j).chart.apply_symm_apply _)
  have hsel (j : Fin 2) : old.pieces (if j = 0 then i else old.mate i) ⊆ A j := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := (hmi j).symm.subset hx
    exact ((B j).chart p).property
  refine ⟨⟨by linarith, tau', A, B, hPL, ?_, hfib, hA, hAI, hdis, ?_, hm, hmi,
    (D.annuli_inter_double_locus A hA hsel).1, ?_⟩⟩
  · intro z hz
    obtain ⟨w, hw, heq⟩ := him.subset (mem_image_of_mem tau' hz)
    exact heq ▸ htauInterior hw
  · rw [him]
    exact hpre
  · intro j s hs u p hp
    have heq : p = ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ := Subtype.ext hp
    rw [heq]
    exact hval j s hs u

end PoincareConjecture.M76.Dehn
