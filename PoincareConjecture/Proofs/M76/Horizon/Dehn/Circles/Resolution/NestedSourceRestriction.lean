import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.NestedRetainedFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceDiskBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedSourceGerms

set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1

theorem nested_retained_open_source_restriction
    {X : Type*} {f g : V2 → X} {m n k : ℕ}
    (P : Polygon V2 (m + 3)) (I : Polygon V2 (n + 3)) (Q : Polygon V2 (k + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hI : I.HasSimplicialEdges) (hinjI : Function.Injective I)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1)
    (hIP : closure I.inside ⊆ P.inside) (hQI : closure Q.inside ⊆ I.inside)
    (H : closure Q.inside ≃ₜ closure I.inside) (hH : H.IsFinitePL)
    (j : (closure Q.inside ∪ (D \ P.inside) : Set V2) → V2)
    (facts : RetainedSquareMapFacts f g _ j)
    (hjQ : ∀ x : closure Q.inside, j ⟨x, Or.inl x.property⟩ = (H x : V2))
    (hjO : ∀ x : ↥(D \ P.inside), j ⟨x, Or.inr x.property⟩ = x)
    (havoid : ∀ x ∈ closure Q.inside ∪ (D \ P.inside),
      x ∈ doubleLocusOn f D → x ∉ closure P.inside \ Q.inside) :
    Nonempty (RetainedSourceOpenHomeomorph f g _ j) := by
  obtain ⟨hcover, hseam, _, _, hclosedC, hclosedO, _⟩ :=
    nested_annulus_source_partition P I hP hinjP hI hinjI hPsq hIP
  obtain ⟨hQball, hiQ, hfQ, _⟩ := polygon_source_region Q
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ convex_univ (subset_univ _)
  obtain ⟨hIball, _, _, _⟩ := polygon_source_region I
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hI hinjI convex_univ (subset_univ _)
  have hQrim : Q.boundary ℝ = closure Q.inside \ Q.inside := by
    rw [← hfQ, frontier, isClosed_closure.closure_eq, hiQ]
  have hK : IsCompact (closure Q.inside ∪ (D \ P.inside)) :=
    hQball.isCompact.union ((isCompact_closedBall _ _).of_isClosed_subset hclosedO sdiff_subset)
  have hB : IsClosed (closure P.inside \ Q.inside) :=
    isClosed_closure.sdiff (hiQ ▸ isOpen_interior)
  have holdcover : D ⊆ (closure Q.inside ∪ (D \ P.inside)) ∪
      (closure P.inside \ Q.inside) := by
    intro x hx
    by_cases hp : x ∈ P.inside
    · by_cases hq : x ∈ Q.inside
      · exact Or.inl (Or.inl (subset_closure hq))
      · exact Or.inr ⟨subset_closure hp, hq⟩
    · exact Or.inl (Or.inr ⟨hx, hp⟩)
  have hnewcover : D ⊆ range j ∪ (closure P.inside \ I.inside) := by
    intro x hx
    rcases hcover.symm.subset hx with (hi | hc) | ho
    · let y := H.symm ⟨x, hi⟩
      refine Or.inl ⟨⟨y, Or.inl y.property⟩, (hjQ y).trans ?_⟩
      exact congrArg Subtype.val (H.apply_symm_apply _)
    · exact Or.inr hc
    · exact Or.inl ⟨⟨x, Or.inr ho⟩, hjO ⟨x, ho⟩⟩
  have hcontact (x : (closure Q.inside ∪ (D \ P.inside) : Set V2))
      (hx : j x ∈ closure P.inside \ I.inside) :
      (x : V2) ∈ closure P.inside \ Q.inside := by
    rcases x.property with hq | ho
    · have hj : j x = (H ⟨x, hq⟩ : V2) := hjQ ⟨x, hq⟩
      have hb : (H ⟨x, hq⟩ : V2) ∈ I.boundary ℝ := hseam ▸
        (show (H ⟨x, hq⟩ : V2) ∈ closure I.inside ∩ (closure P.inside \ I.inside)
          from ⟨(H ⟨x, hq⟩).property, hj ▸ hx⟩)
      have hqb := (finitePL_ball_homeomorph_boundary hQball hIball H hH ⟨x, hq⟩).mp hb
      exact ⟨subset_closure (hIP (subset_closure (hQI hq))), (hQrim ▸ hqb).2⟩
    · have hj : j x = (x : V2) := hjO ⟨x, ho⟩
      exact ⟨(hj ▸ hx).1, fun hq => ho.2 (hIP (subset_closure (hQI (subset_closure hq))))⟩
  exact facts.nonempty_open_source_restriction hK hB hclosedC holdcover hnewcover
    hcontact (fun x hx => havoid x x.property hx)

end Dehn
