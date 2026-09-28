import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.SelectedStep
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.MarkedEndpoints

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q₀" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Q₁" => Set.ofPred (fun x : P2 => depth 8 x = 1)
local notation "Rim" => Q₀ ∪ Q₁

theorem circle_reduction_or_components_meet_boundary
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R F : Set X}
    (hR : IsCompact R) (he : PLDomain e R) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann)
    (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfproper : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgproper : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F ↔ depth 8 x = -1)
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F = {p})
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true))
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false)) :
    (∀ x : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2),
      ∃ y : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier Ann) ∨
    ∃ k : P2 → X, PolyhedralPLInCharts e k Ann ∧
      IsEmbedding (fun x : Ann => k x) ∧ MapsTo k Ann R ∧ EqOn k f (frontier Ann) ∧
      (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      Ann ∩ k ⁻¹' (g '' Ann) ⊆ Ann ∩ f ⁻¹' (g '' Ann) ∧
      (∀ x ∈ Ann ∩ k ⁻¹' (g '' Ann), k x = f x) ∧
      Nat.card (ConnectedComponents (Ann ∩ k ⁻¹' (g '' Ann) : Set P2)) <
        Nat.card (ConnectedComponents (Ann ∩ f ⁻¹' (g '' Ann) : Set P2)) ∧
      (∃ W : Set X, IsOpen W ∧ frontier R ⊆ W ∧
        ∀ z ∈ W, z ∈ k '' Ann ↔ z ∈ f '' Ann) ∧
      (∀ x ∈ Ann ∩ frontier Ann, k x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) true)) ∧
      (∀ x ∈ Ann \ frontier Ann, k x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) false)) := by
  classical
  have hrim : frontier Ann = Rim := Set.ext fun x => mem_frontier_planar_annulus_iff x
  have hrims : ∀ x ∈ Ann, ∀ y ∈ Ann, g x = f y → (x ∈ Rim ↔ y ∈ Rim) := by
    intro x hx y hy hxy
    rw [← hrim,← hgproper x hx,← hfproper y hy,hxy]
  obtain ⟨J,hJ,hJs⟩ := exists_planar_annulus_complex
  obtain ⟨⟨D'⟩,⟨C'⟩⟩ := nonempty_both_surface_intersection_components he.compatible
    J J hJ hJ (hJs.symm ▸ hg) (hJs.symm ▸ hf) (hJs.symm ▸ hgi) (hJs.symm ▸ hfi)
    Rim Rim (by simpa only [hJs] using hrims)
    (by simpa only [hJs,hrim] using hboundary)
    (by simpa only [hJs,hrim] using hinterior)
  have D : SurfaceIntersectionComponents Ann Ann g f Rim := hJs ▸ D'
  have C : SurfaceIntersectionComponents Ann Ann f g Rim := hJs ▸ C'
  by_cases hcircle : ∃ i, Disjoint (C.pieces i) Rim
  · obtain ⟨a,b,_,_,_,_,hfirst_f,hfirst_g⟩ :=
      exists_both_source_first_marked_points hfi hgi hfmark hgmark p hpoint
    obtain ⟨k,hk,hki,hkR,hfront,hproper,hsub,hkeep,hcount,hagree,hcross⟩ :=
      exists_circle_reduction_of_paired_components hR he hf hg hfi hgi hfR hgR
        hfproper hgproper C D b a hfirst_g hfirst_f hcircle hinterior
    refine Or.inr ⟨k,hk,hki,hkR,hfront,hproper,hsub,hkeep,hcount,hagree,?_,?_⟩
    · intro x hx hxg
      have hv := hkeep x ⟨hx.1,hxg⟩
      have hxold : f x ∈ g '' Ann := hv ▸ hxg
      obtain ⟨H⟩ := hboundary x hx hxold
      exact hcross (k x) true ⟨hxg,⟨x,hx.1,rfl⟩⟩ (hv.symm ▸ H)
    · intro x hx hxg
      have hv := hkeep x ⟨hx.1,hxg⟩
      have hxold : f x ∈ g '' Ann := hv ▸ hxg
      obtain ⟨H⟩ := hinterior x hx hxold
      exact hcross (k x) false ⟨hxg,⟨x,hx.1,rfl⟩⟩ (hv.symm ▸ H)
  · exact Or.inl (by simpa only [hrim] using C.components_meet_rim_of_no_closed_piece hcircle)

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
