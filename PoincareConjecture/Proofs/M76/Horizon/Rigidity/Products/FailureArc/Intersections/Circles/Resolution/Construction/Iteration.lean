import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.MarkedStep
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.RimMarks








set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_annulus_with_all_components_meeting_boundary
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R F : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hF : F ⊆ frontier R) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann)
    (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfproper : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgproper : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F ↔ depth 8 x = -1)
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F = {p})
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔
          0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔
          (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k Ann ∧
      IsEmbedding (fun x : Ann => k x) ∧ MapsTo k Ann R ∧ EqOn k f (frontier Ann) ∧
      (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      Ann ∩ k ⁻¹' (g '' Ann) ⊆ Ann ∩ f ⁻¹' (g '' Ann) ∧
      (∀ x ∈ Ann ∩ k ⁻¹' (g '' Ann), k x = f x) ∧
      Nat.card (ConnectedComponents (Ann ∩ k ⁻¹' (g '' Ann) : Set P2)) ≤
        Nat.card (ConnectedComponents (Ann ∩ f ⁻¹' (g '' Ann) : Set P2)) ∧
      (∀ x : (Ann ∩ g ⁻¹' (k '' Ann) : Set P2),
        ∃ y : (Ann ∩ g ⁻¹' (k '' Ann) : Set P2),
          ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier Ann) ∧
      (∀ x ∈ Ann ∩ frontier Ann, k x ∈ g '' Ann →
        ∃ B : OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔
            0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔
            (B.coordinates z).1.2 = 0) ∧
      (∀ x ∈ Ann \ frontier Ann, k x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) false)) := by
  classical
  generalize hn : Nat.card (ConnectedComponents (Ann ∩ f ⁻¹' (g '' Ann) : Set P2)) = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    have hweak : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true) := by
      intro x hx hxy
      obtain ⟨B,_,_⟩ := hboundary x hx hxy
      exact ⟨B⟩
    rcases circle_reduction_or_components_meet_boundary hR he hf hg hfi hgi hfR hgR
      hfproper hgproper hfmark hgmark p hpoint hweak hinterior with hterminal | hstep
    · let : CompactSpace Ann := isCompact_iff_compactSpace.mp isCompact_planar_annulus
      have hemb : IsEmbedding (fun x : Ann => f x) :=
        (hf.continuousOn.domRestrict.isClosedEmbedding
          (fun x y hxy => Subtype.ext (hfi x.property y.property hxy))).isEmbedding
      exact ⟨f,hf,hemb,hfR,fun _ _ => rfl,hfproper,Subset.rfl,fun _ _ => rfl,
        hn.le,hterminal,hboundary,hinterior⟩
    · obtain ⟨k,hk,hki,hkR,hfront,hproper,hsub,hkeep,hcount,⟨W,hW,hFW,hWvalue⟩,
        _,hkinterior⟩ := hstep
      have hkinj : InjOn k Ann := by
        intro x hx y hy hxy
        exact congrArg Subtype.val (hki.injective (show
          (fun z : Ann => k z) ⟨x,hx⟩ = (fun z : Ann => k z) ⟨y,hy⟩ from hxy))
      have hkmark : ∀ x ∈ Ann, k x ∈ F ↔ depth 8 x = -1 := by
        intro x hx
        exact (proper_rim_fixed_mark_iff hF hfproper hproper hfront x hx).trans (hfmark x hx)
      have hkpoint : ((k '' Ann) ∩ (g '' Ann)) ∩ F = {p} :=
        (proper_rim_fixed_marked_intersection hF hfproper hproper hfront).trans hpoint
      have hkboundary : ∀ x ∈ Ann ∩ frontier Ann, k x ∈ g '' Ann →
          ∃ B : OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) true,
            (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔
              0 ≤ (B.coordinates z).1.2) ∧
            ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔
              (B.coordinates z).1.2 = 0 := by
        intro x hx hxy
        have hv := hfront hx.2
        obtain ⟨B,hBR,hBF⟩ := hboundary x hx (hv ▸ hxy)
        have hyW : f x ∈ W := hFW ((hfproper x hx.1).mpr hx.2)
        obtain ⟨B',hB'R,hB'F⟩ := boundary_pair_chart_of_local_agreement B hBR hBF hW hyW hWvalue
        exact hv.symm ▸ ⟨B',hB'R,hB'F⟩
      have hlt : Nat.card (ConnectedComponents (Ann ∩ k ⁻¹' (g '' Ann) : Set P2)) < n :=
        hn ▸ hcount
      obtain ⟨k',hk',hki',hkR',hfront',hproper',hsub',hkeep',hcount',hterminal',hboundary',hinterior'⟩ :=
        ih _ hlt hk hkinj hkR hproper hkmark hkpoint hkboundary hkinterior rfl
      refine ⟨k',hk',hki',hkR',fun x hx => (hfront' hx).trans (hfront hx),hproper',
        hsub'.trans hsub,?_,hcount'.trans hlt.le,hterminal',hboundary',hinterior'⟩
      intro x hx
      exact (hkeep' x hx).trans (hkeep x (hsub' hx))

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
