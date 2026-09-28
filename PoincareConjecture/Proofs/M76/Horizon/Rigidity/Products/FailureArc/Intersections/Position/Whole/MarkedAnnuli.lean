import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.FromBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.MarkedMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.RimAnchors
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.AnnulusCarrier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.RetainedCharts

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem exists_original_marked_position_of_boundary_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (mark : Bool → Set X)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hmark : ∀ b, mark b ⊆ frontier R)
    (hcomponent : ∀ b y, y ∈ mark b → connectedComponentIn (frontier R) y = mark b)
    {f g : P2 → X} (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann)
    (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfl : ∀ x ∈ Ann, f x ∈ mark false ↔ depth 8 x = -1)
    (hfu : MapsTo f (Ann ∩ Last) (mark true))
    (p : X) (hp : ((f '' Ann) ∩ (g '' Ann)) ∩ mark false = {p})
    (hboundary : ∀ x ∈ frontier Ann, g x ∈ f '' Ann →
      ∃ C : OriginalSurfacePairChart e (f '' Ann) (g '' Ann) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) :
    ∃ (k : P2 → X) (q : X),
      PolyhedralPLInCharts e k Ann ∧ InjOn k Ann ∧ MapsTo k Ann R ∧
      (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      (∀ x ∈ Ann, k x ∈ mark false ↔ depth 8 x = -1) ∧
      MapsTo k (Ann ∩ Last) (mark true) ∧
      ((k '' Ann) ∩ (g '' Ann)) ∩ mark false = {q} ∧
      (∀ x ∈ Ann ∩ frontier Ann, k x ∈ g '' Ann →
        ∃ C : OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) true,
          (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0) ∧
      ∀ x ∈ Ann \ frontier Ann, k x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) false) := by
  classical
  obtain ⟨K, hK, hKs⟩ := exists_planar_annulus_complex
  have hfK : PolyhedralPLInCharts e f K.space := hKs.symm ▸ hf
  have hgK : PolyhedralPLInCharts e g K.space := hKs.symm ▸ hg
  have hfKi : InjOn f K.space := hKs.symm ▸ hfi
  have hboundK : ∀ x ∈ K.space, g x ∈ frontier R → g x ∈ f '' K.space →
      ∃ C : OriginalSurfacePairChart e (f '' K.space) (g '' K.space) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
    rw [hKs]
    exact fun x hx hxR => hboundary x ((hgp x hx).mp hxR)
  obtain ⟨a, hamark, ha, haT, haClosed⟩ := exists_source_rim_anchors_outside_target
    K K hK hK hKs hfK.continuousOn hfKi hgK.continuousOn
    (fun x hx => hfp x (hKs.subset hx)) (by
      intro b z
      cases b
      · exact (hfl _ (annulusRimPoint false z).property).mpr (depth_annulusRimPoint false z)
      · exact hfu ⟨(annulusRimPoint true z).property, depth_annulusRimPoint true z⟩) hboundK
  have hpdata := hp.symm.subset (mem_singleton p)
  have hmeet : ((f '' K.space) ∩ (g '' frontier Ann)).Nonempty := by
    obtain ⟨x, hx, hxp⟩ := hpdata.1.2
    exact ⟨p, hKs.symm ▸ hpdata.1.1, x,
      (hgp x hx).mp (hxp.symm ▸ hmark false hpdata.2), hxp⟩
  obtain ⟨H, k, hk, hki, hkR, hkp, hkrim, _, _, hHT, hHR, hHfix, hkb, hkiCharts, _⟩ :=
    exists_original_annulus_position_of_boundary_charts hcover he K K hK hK hKs
      hfK hgK hfKi (hKs.symm ▸ hgi) R (hKs.symm ▸ hfR) (hKs.symm ▸ hgR)
      (by simpa only [hKs] using hfp) (fun x hx => hgp x (hKs.subset hx))
      (hKs.symm ▸ isPreconnected_planar_annulus_without_frontier)
      (by rw [hKs]; exact hboundary) hmeet haClosed haT
  have hHmarks (b : Bool) : H ⁻¹' mark b = mark b :=
    preimage_boundary_component_of_fixed_anchor H hHR (ha b).2
      (hcomponent b (a b) (hamark b)) (hHfix (mem_range_self b))
  have hkAnn : PolyhedralPLInCharts e k Ann := hKs ▸ hk
  have hkpAnn : ∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann := by simpa only [hKs] using hkp
  have hrimAnn : EqOn k (H ∘ f) (Ann ∩ frontier Ann) := by simpa only [hKs] using hkrim
  have hmarkEq (b : Bool) : ∀ x ∈ Ann, k x ∈ mark b ↔ f x ∈ mark b :=
    boundary_marks_of_proper_rim_agreement H (hmark b) (hHmarks b) hfp hkpAnn hrimAnn
  have hHTAnn : H ⁻¹' (g '' Ann) = g '' Ann := by simpa only [hKs] using hHT
  have hpointNew : ((k '' Ann) ∩ (g '' Ann)) ∩ mark false = {H p} := by
    rw [marked_intersections_of_proper_rim_agreement H (hmark false) (hHmarks false)
      hHTAnn hfp hkpAnn hrimAnn, hp, image_singleton]
  have hboundaryAnn : ∀ x ∈ frontier Ann, g x ∈ k '' Ann →
      ∃ C : OriginalSurfacePairChart e (k '' Ann) (g '' Ann) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
    rw [hKs] at hkb
    exact hkb
  refine ⟨k, H p, hkAnn, hKs ▸ hki, hKs ▸ hkR, hkpAnn,
    (fun x hx => (hmarkEq false x hx).trans (hfl x hx)),
    (fun x hx => (hmarkEq true x hx.1).mpr (hfu hx)), hpointNew, ?_, ?_⟩
  · intro x hx hxg
    obtain ⟨y, hy, hyx⟩ := hxg
    have hyrim := (hgp y hy).mp (hyx.symm ▸ (hkpAnn x hx.1).mpr hx.2)
    obtain ⟨C, hC⟩ := hboundaryAnn y hyrim (hyx.symm ▸ mem_image_of_mem k hx.1)
    rw [← hyx]
    exact C.swap_boundary_region hC (C.frontier_iff_of_region_halfspace hC)
  · intro x hx hxg
    obtain ⟨y, hy, hyx⟩ := hxg
    have hyint : y ∈ interior Ann := by
      by_contra hn
      have hyrim : y ∈ frontier Ann := ⟨subset_closure hy, hn⟩
      exact hx.2 ((hkpAnn x hx.1).mp (hyx ▸ (hgp y hy).mpr hyrim))
    rw [hKs] at hkiCharts
    obtain ⟨C⟩ := hkiCharts y hyint (hyx.symm ▸ mem_image_of_mem k hx.1)
    rw [← hyx]
    exact ⟨C.swap⟩

end PoincareConjecture.M76
