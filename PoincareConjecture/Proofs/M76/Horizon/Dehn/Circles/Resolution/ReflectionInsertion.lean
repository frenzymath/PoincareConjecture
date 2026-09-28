import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.InPlaceReplacement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.BoundaryMatchedReflectionAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusFrontier
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
open Dehn

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_reflection_insertion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (he : PLDomain e R)
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (τ : (P2 × ℝ) → X) (hτ : PolyhedralPLInCharts e τ (singleReflectionTube L d))
    (hfib : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
      τ z = τ w ↔ z = w ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0))))
    (hτR : τ '' singleReflectionTube L d ⊆ interior R)
    {T : Set V2} (hT : T ⊆ interior D2)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL)
    (hsource : ∀ s ∈ Icc 0 (4 * L), ∀ u : Icc (-d) d,
      f (c ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩) =
        if s ≤ 2 * L then τ ((u, u), s) else τ ((u, -u), s - 2 * L))
    (hpreimage : D2 ∩ f ⁻¹' (τ '' singleReflectionTube L d) = T)
    (i : old.Index) (htrace : T ∩ doubleLocusOn f D2 = old.pieces i)
    (haxis : ∀ p : squareAnnulus L d, (c p : V2) ∈ old.pieces i ↔ depth L p = 0) :
    ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  have hL : 0 < L := by linarith
  have hdim : Module.finrank ℝ P2 = Module.finrank ℝ V2 := by simp
  obtain ⟨g, hg, hgemb, hgimage, hgcurves, _⟩ :=
    _root_.Dehn.exists_boundary_matched_reflection_annulus e he.compatible
      hd hwidth hb hbd τ hτ hfib
  obtain ⟨q, hq, hqval⟩ := hc.symm
  have hqmap : MapsTo q T (squareAnnulus L d) := by
    intro x hx
    rw [← hqval ⟨x, hx⟩]
    exact (c.symm ⟨x, hx⟩).property
  obtain ⟨A, hA, hAs, hAff⟩ := hq
  have ha : PolyhedralPLInCharts e (g ∘ q) A.space :=
    hg.comp_finitePiecewiseAffineOn A hA ⟨A, hA, rfl, hAff⟩ (hAs.symm ▸ hqmap)
  have haj : InjOn (g ∘ q) A.space := by
    intro x hx y hy hxy
    have heq : q x = q y := congrArg Subtype.val
      (hgemb.injective (a₁ := ⟨q x, hqmap (hAs.subset hx)⟩)
        (a₂ := ⟨q y, hqmap (hAs.subset hy)⟩) hxy)
    rw [← hqval ⟨x, hAs.subset hx⟩, ← hqval ⟨y, hAs.subset hy⟩] at heq
    exact congrArg Subtype.val (c.symm.injective (Subtype.ext heq))
  have haimage : (g ∘ q) '' A.space ⊆ τ '' singleReflectionTube L d := by
    rintro _ ⟨x, hx, rfl⟩
    exact hgimage ⟨q x, hqmap (hAs.subset hx), rfl⟩
  have haR : MapsTo (g ∘ q) A.space (interior R) :=
    fun x hx ↦ hτR (haimage ⟨x, hx, rfl⟩)
  obtain ⟨J, hJ, hJs⟩ := SimplicialComplex.exists_finite_coordinate_closedBall
    (0 : V2) (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨K, hK, hKs, hcover, hseam⟩ :=
    _root_.Dehn.exists_finite_interior_carrier_complement J A hJ hA
      (by rw [hJs, hAs]; exact hT)
  rw [hJs] at hKs hcover
  have hAQ : Disjoint A.space Q2 := by
    apply disjoint_left.mpr
    intro x hx hxQ
    have hxint := hT (hAs.subset hx)
    rw [interior_closedBall _ one_ne_zero] at hxint
    exact ne_of_lt (mem_ball.mp hxint) (mem_sphere.mp hxQ)
  have hagree : ∀ x ∈ K.space, x ∈ A.space → f x = (g ∘ q) x := by
    intro x hxK hxA
    have hxfront : x ∈ frontier T := hAs ▸ hseam.subset ⟨hxK, hxA⟩
    let p := c.symm ⟨x, hAs.subset hxA⟩
    have hcp : (c p : V2) = x := congrArg Subtype.val (c.apply_symm_apply _)
    have hpfront : (p : P2) ∈ frontier (squareAnnulus L d) :=
      (hc.mem_frontier_iff_of_finrank_eq hdim p).mp (hcp.symm ▸ hxfront)
    have hpabs := (mem_frontier_squareAnnulus_iff hd (by linarith) p.property).mp hpfront
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    have hsourcep : f x = if s ≤ 2 * L then τ ((depth L p, depth L p), s)
        else τ ((depth L p, -depth L p), s - 2 * L) := by
      have hh := hsource s hs ⟨depth L p, mem_squareAnnulus_iff_depth.mp p.property⟩
      have hpp : (⟨annulusMap L hL ((s : AddCircle (4 * L)), depth L p),
          _root_.Dehn.annulus_period_point_mem hd hwidth _
            ⟨depth L p, mem_squareAnnulus_iff_depth.mp p.property⟩⟩ : squareAnnulus L d) = p :=
        Subtype.ext hsp.symm
      simpa only [hpp, hcp] using hh
    change f x = g (q x)
    rw [← hqval ⟨x, hAs.subset hxA⟩]
    change f x = g p
    rw [hsp, hsourcep]
    rcases (abs_eq hd.le).mp hpabs with hp | hp
    · rw [hp]
      exact (hgcurves s hs).2.symm
    · rw [hp]
      simpa only [neg_neg] using (hgcurves s hs).1.symm
  have hcross : ∀ x ∈ A.space, ∀ y ∈ K.space, (g ∘ q) x = f y → x = y := by
    intro x hx y hy hxy
    have hyD : y ∈ D2 := hcover.subset (Or.inl hy)
    have hyTube : f y ∈ τ '' singleReflectionTube L d :=
      hxy ▸ haimage ⟨x, hx, rfl⟩
    have hyT : y ∈ T := hpreimage.subset ⟨hyD, hyTube⟩
    exact haj hx (hAs.symm.subset hyT) (hxy.trans (hagree y hy (hAs.symm.subset hyT)))
  have hremoved : Disjoint K.space (old.pieces i) := by
    apply disjoint_left.mpr
    intro x hxK hxi
    have hxT : x ∈ T := (htrace.symm.subset hxi).1
    let p := c.symm ⟨x, hxT⟩
    have hcp : (c p : V2) = x := congrArg Subtype.val (c.apply_symm_apply _)
    have hpzero := (haxis p).mp (hcp.symm ▸ hxi)
    have hpint : (p : P2) ∈ interior (squareAnnulus L d) := by
      rw [interior_squareAnnulus (by linarith)]
      change -d < depth L p ∧ depth L p < d
      rw [hpzero]
      exact ⟨by linarith, hd⟩
    have hxint : x ∈ interior T := hcp ▸ (hc.mem_interior_iff_of_finrank_eq hdim p).mpr hpint
    exact (hKs.subset hxK).2 (hAs.symm ▸ hxint)
  obtain ⟨out, hout, _, _, houtR, hboundary, hproper, _, hbc, hic, model⟩ :=
    old.exists_in_place_circle_resolution hf he hin hfront K A hK hA hcover hAQ
      (g ∘ q) ha haR haj hagree hcross i (by rw [hAs]; exact htrace) hremoved
  exact ⟨out, hout, houtR, hboundary, hproper, hbc, hic, model⟩

end PoincareConjecture.M76.Dehn
