import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.Iteration
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Intersections.SingleSpanningComponent



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem exists_literal_spanning_interval_of_components_meet_first_rim
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (F : Bool → Set X)
    (he : PLDomain e R) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgmark : ∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1)
    (hglast : MapsTo g (Ann ∩ Last) (F true))
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {p})
    (hmeet : ∀ x : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2),
      ∃ y : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ depth 8 (y : P2) = -1)
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true))
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false)) :
    IsFinitePLBallPair ℝ (Ann ∩ g ⁻¹' (f '' Ann))
      ((Ann ∩ g ⁻¹' (f '' Ann)) ∩ frontier Ann) ∧
    ∃ H : unitInterval ≃ₜ (Ann ∩ g ⁻¹' (f '' Ann) : Set P2),
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧ g (H 0) = p ∧ g (H 1) ∈ F true ∧
      (∀ t : unitInterval, g (H t) ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
      (∀ t : unitInterval, g (H t) ∈ F false ↔ t = 0) ∧
      Nat.card (ConnectedComponents (Ann ∩ g ⁻¹' (f '' Ann) : Set P2)) = 1 := by
  classical
  obtain ⟨J, hJ, hJs⟩ := exists_planar_annulus_complex
  have hrims : ∀ x ∈ Ann, ∀ y ∈ Ann, g x = f y →
      (x ∈ frontier Ann ↔ y ∈ frontier Ann) := by
    intro x hx y hy hxy
    rw [← hgp x hx, ← hfp y hy, hxy]
  obtain ⟨_, ⟨C'⟩⟩ := nonempty_both_surface_intersection_components he.compatible
    J J hJ hJ (hJs.symm ▸ hg) (hJs.symm ▸ hf) (hJs.symm ▸ hgi) (hJs.symm ▸ hfi)
    (frontier Ann) (frontier Ann) (hJs.symm ▸ hrims)
    (hJs.symm ▸ hboundary) (hJs.symm ▸ hinterior)
  have C : SurfaceIntersectionComponents Ann Ann f g (frontier Ann) := hJs ▸ C'
  have hright : ∀ x : C.right.space, ∃ y : C.right.space,
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ depth 8 (y : P2) = -1 := by
    rw [C.right_space]
    exact hmeet
  have hreaches : ∀ i, ∃ y ∈ C.pieces i, g y ∈ F false := by
    intro i
    obtain ⟨x, hx⟩ := (C.topology i).2.1.nonempty
    have hxS := C.cover.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)
    obtain ⟨y, hxy, hyFirst⟩ := hright ⟨x, hxS⟩
    have hxi := (C.intrinsic_value ⟨x, hxS⟩ i).mpr hx
    have hyi : (y : P2) ∈ C.pieces i := (C.intrinsic_value y i).mp
      ((congrArg C.intrinsic hxy).symm.trans hxi)
    exact ⟨y, hyi, (hgmark y (C.right_space.subset y.property).1).mpr hyFirst⟩
  have hrim : ∀ y ∈ C.right.space, g y ∈ F false → y ∈ frontier Ann := by
    intro y hy hmark
    exact (mem_frontier_planar_annulus_iff y).mpr
      (Or.inl ((hgmark y (C.right_space.subset hy).1).mp hmark))
  obtain ⟨_, _, _, _, _, hball, _⟩ :=
    C.exists_single_spanning_interval hgi (F false) p hpoint hreaches hrim
  obtain ⟨H, hH, hHi, h0, h1, hbound, hmark⟩ :=
    C.exists_marked_spanning_interval_parametrization hgi (F false) p hpoint hreaches hrim
  have hlast : g (H 1) ∈ F true := by
    have hyAnn := (C.right_space.subset (H 1).property).1
    have hdepth := (mem_frontier_planar_annulus_iff (H 1)).mp ((hbound 1).mpr (Or.inr rfl))
    rcases hdepth with hfirst | hlast
    · exact (h1 ((hgmark (H 1) hyAnn).mpr hfirst)).elim
    · exact hglast ⟨hyAnn, hlast⟩
  have hproper (t : unitInterval) : g (H t) ∈ frontier R ↔ t = 0 ∨ t = 1 :=
    (hgp (H t) (C.right_space.subset (H t).property).1).trans (hbound t)
  have hcount := C.component_card_eq_one_of_single_mark hgi (F false) p hpoint hreaches hrim
  have hh : IsFinitePLBallPair ℝ C.right.space (C.right.space ∩ frontier Ann) ∧
      ∃ H : unitInterval ≃ₜ C.right.space,
        H.IsFinitePL ∧ H.symm.IsFinitePL ∧ g (H 0) = p ∧ g (H 1) ∈ F true ∧
        (∀ t : unitInterval, g (H t) ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
        (∀ t : unitInterval, g (H t) ∈ F false ↔ t = 0) ∧
        Nat.card (ConnectedComponents C.right.space) = 1 :=
    ⟨hball, H, hH, hHi, h0, hlast, hproper, hmark, hcount⟩
  rw [C.right_space] at hh
  exact hh

end PoincareConjecture.M76.Dehn.Annuli
