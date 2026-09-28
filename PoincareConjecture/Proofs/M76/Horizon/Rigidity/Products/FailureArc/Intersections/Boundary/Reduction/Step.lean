import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.Selected
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Source.MarkedPoint

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem returning_reduction_or_components_meet_protected_rim
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (F : Bool → Set X)
    (hR : IsCompact R) (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F true))
    (hFdis : Disjoint (F false) (F true))
    {H T : Set P2} (hH : IsFinitePLBallPair P2 H (frontier H))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hHT : H ⊆ interior T)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite) (hJs : J.space = T \ interior H)
    {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f J.space) (hg : PolyhedralPLInCharts e g J.space)
    (hfi : InjOn f J.space) (hgi : InjOn g J.space)
    (hfR : MapsTo f J.space R) (hgR : MapsTo g J.space R)
    (hfp : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier T ∪ frontier H)
    (hgp : ∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier T ∪ frontier H)
    (hfmark : ∀ x ∈ J.space, f x ∈ F false ↔ x ∈ frontier H)
    (hgmark : ∀ x ∈ J.space, g x ∈ F false ↔ x ∈ frontier H)
    (hfouter : MapsTo f (J.space ∩ frontier T) (F true))
    (hgouter : MapsTo g (J.space ∩ frontier T) (F true))
    (p : X) (hpoint : ((f '' J.space) ∩ (g '' J.space)) ∩ F false = {p})
    (hmeet : ∀ x : (J.space ∩ g ⁻¹' (f '' J.space) : Set P2),
      ∃ y : (J.space ∩ g ⁻¹' (f '' J.space) : Set P2),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier T ∪ frontier H)
    (hboundary : ∀ x ∈ J.space, f x ∈ g '' J.space → f x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f '' J.space) (g '' J.space) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ J.space, f x ∈ g '' J.space → f x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f '' J.space) (g '' J.space) (f x) false)) :
    (∀ x : (J.space ∩ g ⁻¹' (f '' J.space) : Set P2),
      ∃ y : (J.space ∩ g ⁻¹' (f '' J.space) : Set P2),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier H) ∨
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space ↦ k x) ∧ MapsTo k J.space R ∧
      EqOn k f (J.space ∩ frontier H) ∧ MapsTo k (J.space ∩ frontier T) (F true) ∧
      (∀ x ∈ J.space, k x ∈ frontier R ↔ x ∈ frontier T ∪ frontier H) ∧
      (∀ x ∈ J.space, k x ∈ F false ↔ x ∈ frontier H) ∧
      ((k '' J.space) ∩ (g '' J.space)) ∩ F false = {p} ∧
      J.space ∩ k ⁻¹' (g '' J.space) ⊆ J.space ∩ f ⁻¹' (g '' J.space) ∧
      EqOn k f (J.space ∩ k ⁻¹' (g '' J.space)) ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (g '' J.space) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f ⁻¹' (g '' J.space) : Set P2)) ∧
      (∀ x ∈ J.space, k x ∈ g '' J.space → k x ∈ frontier R →
        ∃ B : OriginalSurfacePairChart e (k '' J.space) (g '' J.space) (k x) true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
      ∀ x ∈ J.space, k x ∈ g '' J.space → k x ∈ interior R →
        Nonempty (OriginalSurfacePairChart e (k '' J.space) (g '' J.space) (k x) false) := by
  classical
  let rim := frontier H ∪ frontier T
  have hrims : ∀ x ∈ J.space, ∀ y ∈ J.space, f x = g y → (x ∈ rim ↔ y ∈ rim) := by
    intro x hx y hy hxy
    change x ∈ frontier H ∪ frontier T ↔ y ∈ frontier H ∪ frontier T
    rw [union_comm (frontier H), ← hfp x hx, ← hgp y hy, hxy]
  have hbg : ∀ y ∈ J.space ∩ rim, g y ∈ f '' J.space →
      Nonempty (OriginalSurfacePairChart e (f '' J.space) (g '' J.space) (g y) true) := by
    intro y hy hgf
    obtain ⟨x, hx, hxy⟩ := hgf
    have hyfront : g y ∈ frontier R := (hgp y hy.1).mpr (by
      simpa only [rim, union_comm] using hy.2)
    obtain ⟨B, _, _⟩ := hboundary x hx ⟨y, hy.1, hxy.symm⟩ (hxy.symm ▸ hyfront)
    exact hxy ▸ ⟨B⟩
  have hig : ∀ y ∈ J.space \ rim, g y ∈ f '' J.space →
      Nonempty (OriginalSurfacePairChart e (f '' J.space) (g '' J.space) (g y) false) := by
    intro y hy hgf
    obtain ⟨x, hx, hxy⟩ := hgf
    have hyint : g y ∈ interior R := by
      by_contra hn
      have hyfront : g y ∈ frontier R := ⟨subset_closure (hgR hy.1), hn⟩
      exact hy.2 (by simpa only [rim, union_comm] using (hgp y hy.1).mp hyfront)
    obtain ⟨B⟩ := hinterior x hx ⟨y, hy.1, hxy.symm⟩ (hxy.symm ▸ hyint)
    exact hxy ▸ ⟨B⟩
  obtain ⟨⟨C'⟩, ⟨D'⟩⟩ := nonempty_both_surface_intersection_components he.compatible
    J J hJ hJ hf hg hfi hgi rim rim hrims hbg hig
  have C : SurfaceIntersectionComponents (T \ interior H) (T \ interior H) f g rim := hJs ▸ C'
  have D : SurfaceIntersectionComponents (T \ interior H) (T \ interior H) g f rim := hJs ▸ D'
  by_cases hreturn : ∃ i, Disjoint (C.pieces i) (frontier H)
  · obtain ⟨a, ha⟩ := exists_first_source_point_of_marked_intersection hgi hgmark p hpoint
    have hfirst : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H))) ∩ frontier H = {a} := by
      simpa only [hJs] using ha
    have hprotected : ∀ x ∈ J.space, ∀ y ∈ J.space, f x = g y →
        (x ∈ frontier H ↔ y ∈ frontier H) := by
      intro x hx y hy hxy
      rw [← hfmark x hx, ← hgmark y hy, hxy]
    have hmeet' : ∀ x : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H)) : Set P2),
        ∃ y : ((T \ interior H) ∩ g ⁻¹' (f '' (T \ interior H)) : Set P2),
          ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier H ∪ frontier T := by
      have hh := hmeet
      rw [hJs] at hh
      simpa only [union_comm] using hh
    obtain ⟨k, hk, hki, hkR, hkH, hkF, hkproper, hksub, hkkeep, hkcount, hkb, hki'⟩ :=
      exists_returning_reduction_of_paired_components hR he (hF true) hFopen hH hT hHT J hJ hJs
        hf hg hfi hgi hfR hgR hfp hgp hfouter hgouter hprotected C D a hfirst hmeet'
        hreturn hboundary hinterior
    have hkmark := protected_mark_iff_of_boundary_replacement (hF false) hFdis hkproper hkH hkF hfmark
    have hkpoint := (protected_marked_intersection_of_boundary_replacement hkH hfmark hkmark).trans hpoint
    exact Or.inr ⟨k, hk, hki, hkR, hkH, hkF, hkproper, hkmark, hkpoint,
      hksub, hkkeep, hkcount, hkb, hki'⟩
  · apply Or.inl
    rw [hJs]
    exact C.components_meet_set_of_no_disjoint_piece hreturn

end PoincareConjecture.M76.Dehn.Annuli
