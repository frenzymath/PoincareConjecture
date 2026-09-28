import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.DisjointRetainedFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceDiskBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedSourceGerms









set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1

theorem disjoint_retained_open_source_restriction
    {X : Type*} {f g : V2 → X} {m n : Bool → ℕ}
    (P : (i : Bool) → Polygon V2 (m i + 3)) (I : (i : Bool) → Polygon V2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hinjP : ∀ i, Function.Injective (P i))
    (hI : ∀ i, (I i).HasSimplicialEdges) (hinjI : ∀ i, Function.Injective (I i))
    (hPsq : ∀ i, (P i).boundary ℝ ⊆ ball 0 1)
    (hIP : ∀ i, closure (I i).inside ⊆ (P i).inside)
    (hdisP : Disjoint (closure (P false).inside) (closure (P true).inside))
    (H : closure (I false).inside ≃ₜ closure (I true).inside) (hH : H.IsFinitePL)
    (j : ((closure (I false).inside ∪ closure (I true).inside) ∪
      (D \ ((P false).inside ∪ (P true).inside)) : Set V2) → V2)
    (facts : RetainedSquareMapFacts f g _ j)
    (hrange : range j = (closure (I false).inside ∪ closure (I true).inside) ∪
      (D \ ((P false).inside ∪ (P true).inside)))
    (hj0 : ∀ x : closure (I false).inside,
      j ⟨x, Or.inl (Or.inl x.property)⟩ = (H x : V2))
    (hj1 : ∀ x : closure (I true).inside,
      j ⟨x, Or.inl (Or.inr x.property)⟩ = (H.symm x : V2))
    (hjO : ∀ x : ↥(D \ ((P false).inside ∪ (P true).inside)), j ⟨x, Or.inr x.property⟩ = x)
    (havoid : ∀ x ∈ (closure (I false).inside ∪ closure (I true).inside) ∪
        (D \ ((P false).inside ∪ (P true).inside)),
      x ∈ doubleLocusOn f D → x ∉ (closure (P false).inside \ (I false).inside) ∪
        (closure (P true).inside \ (I true).inside)) :
    Nonempty (RetainedSourceOpenHomeomorph f g _ j) := by
  let S := fun i => closure (I i).inside
  let C := fun i => closure (P i).inside \ (I i).inside
  let O := D \ ((P false).inside ∪ (P true).inside)
  let K := (S false ∪ S true) ∪ O
  obtain ⟨hcover, hseam, _, _, _, _, hdisIC, hclosedC, hclosedO, _, _, _⟩ :=
    disjoint_annulus_source_partition P I hP hinjP hI hinjI hPsq hIP hdisP
  have hregions (i : Bool) := polygon_source_region (I i)
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) (hI i) (hinjI i) convex_univ (subset_univ _)
  have hrim (i : Bool) : (I i).boundary ℝ = S i \ (I i).inside := by
    rw [← (hregions i).2.2.1, frontier, isClosed_closure.closure_eq, (hregions i).2.1]
  have hbC (i : Bool) : (I i).boundary ℝ ⊆ C i := by
    intro x hx
    rw [hrim] at hx
    exact ⟨subset_closure (hIP i hx.1), hx.2⟩
  have hK : IsCompact K :=
    ((hregions false).1.isCompact.union (hregions true).1.isCompact).union
      ((isCompact_closedBall _ _).of_isClosed_subset hclosedO sdiff_subset)
  have hcontact (x : K) (hx : j x ∈ C false ∪ C true) : (x : V2) ∈ C false ∪ C true := by
    rcases x.property with (hx0 | hx1) | hxo
    · have hj : j x = (H ⟨x, hx0⟩ : V2) := hj0 ⟨x, hx0⟩
      rw [hj] at hx
      rcases hx with hc0 | hc1
      · exact False.elim (disjoint_left.mp (hdisIC false) (H ⟨x, hx0⟩).property hc0)
      · have hb : (H ⟨x, hx0⟩ : V2) ∈ (I true).boundary ℝ :=
          hseam true ▸ ⟨(H ⟨x, hx0⟩).property, hc1⟩
        exact Or.inl (hbC false ((finitePL_ball_homeomorph_boundary
          (hregions false).1 (hregions true).1 H hH ⟨x, hx0⟩).mp hb))
    · have hj : j x = (H.symm ⟨x, hx1⟩ : V2) := hj1 ⟨x, hx1⟩
      rw [hj] at hx
      rcases hx with hc0 | hc1
      · have hb : (H.symm ⟨x, hx1⟩ : V2) ∈ (I false).boundary ℝ :=
          hseam false ▸ ⟨(H.symm ⟨x, hx1⟩).property, hc0⟩
        exact Or.inr (hbC true ((finitePL_ball_homeomorph_boundary
          (hregions true).1 (hregions false).1 H.symm hH.symm ⟨x, hx1⟩).mp hb))
      · exact False.elim (disjoint_left.mp (hdisIC true) (H.symm ⟨x, hx1⟩).property hc1)
    · exact (show j x = (x : V2) from hjO ⟨x, hxo⟩) ▸ hx
  apply facts.nonempty_open_source_restriction hK
    ((hclosedC false).union (hclosedC true)) ((hclosedC false).union (hclosedC true))
    hcover.symm.subset
  · rw [hrange]
    exact hcover.symm.subset
  · exact hcontact
  · exact fun x hx => havoid x x.property hx

end Dehn
