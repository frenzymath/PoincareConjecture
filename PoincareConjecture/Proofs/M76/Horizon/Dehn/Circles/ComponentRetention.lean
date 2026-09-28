import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts

set_option autoImplicit false

open Set Metric Geometry

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem component_sides_of_disjoint_frontier
    {E : Type*} [TopologicalSpace E] {K A : Set E}
    (hK : IsPreconnected K) (hA : IsClosed A) (havoid : Disjoint K (frontier A)) :
    K ⊆ interior A ∨ K ⊆ Aᶜ := by
  apply hK.subset_or_subset isOpen_interior hA.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset)
  intro x hx
  by_cases hxA : x ∈ A
  · by_cases hxi : x ∈ interior A
    · exact Or.inl hxi
    · exact False.elim (disjoint_left.mp havoid hx ⟨subset_closure hxA, hxi⟩)
  · exact Or.inr hxA

def NestedCircleComponentLocation {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3)) (K : Set V2) : Prop :=
  (K ⊆ Q.inside ∧ Disjoint K (D2 \ P.inside)) ∨
    (K ⊆ D2 \ closure P.inside ∧ Disjoint K (closure Q.inside)) ∨
    (K ⊆ P.inside \ closure Q.inside ∧
      Disjoint K (closure Q.inside ∪ (D2 \ P.inside)))

def DisjointCircleComponentLocation {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3)) (K : Set V2) : Prop :=
  (K ⊆ P.inside ∧ Disjoint K (closure Q.inside) ∧
    Disjoint K (D2 \ (P.inside ∪ Q.inside))) ∨
    (K ⊆ Q.inside ∧ Disjoint K (closure P.inside) ∧
      Disjoint K (D2 \ (P.inside ∪ Q.inside))) ∨
    K ⊆ D2 \ (closure P.inside ∪ closure Q.inside)

theorem nested_circle_component_location {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (hnest : closure Q.inside ⊆ P.inside)
    {K : Set V2} (hK : IsPreconnected K) (hKD : K ⊆ D2)
    (hKP : Disjoint K (P.boundary ℝ)) (hKQ : Disjoint K (Q.boundary ℝ)) :
    NestedCircleComponentLocation P Q K := by
  obtain ⟨_, hiP, hfP, _⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
  obtain ⟨_, hiQ, hfQ, _⟩ := polygon_source_region Q
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ (convex_ball _ _) hQsq
  have hsideP := component_sides_of_disjoint_frontier hK isClosed_closure (hfP ▸ hKP)
  have hsideQ := component_sides_of_disjoint_frontier hK isClosed_closure (hfQ ▸ hKQ)
  rw [hiP] at hsideP
  rw [hiQ] at hsideQ
  rcases hsideQ with hQin | hQout
  · exact Or.inl ⟨hQin, disjoint_left.mpr
      (fun x hx hxout ↦ hxout.2 (hnest (subset_closure (hQin hx))))⟩
  · rcases hsideP with hPin | hPout
    · refine Or.inr (Or.inr ⟨fun x hx ↦ ⟨hPin hx, hQout hx⟩, ?_⟩)
      apply disjoint_left.mpr
      intro x hx hret
      rcases hret with hq | hp
      · exact hQout hx hq
      · exact hp.2 (hPin hx)
    · refine Or.inr (Or.inl ⟨fun x hx ↦ ⟨hKD hx, hPout hx⟩, ?_⟩)
      exact disjoint_left.mpr (fun x hx hq ↦ hPout hx (subset_closure (hnest hq)))

theorem NestedCircleComponentLocation.retained_or_disjoint {m n : ℕ}
    {P : Polygon V2 (m + 3)} {Q : Polygon V2 (n + 3)} {K : Set V2}
    (h : NestedCircleComponentLocation P Q K) :
    K ⊆ closure Q.inside ∪ (D2 \ P.inside) ∨
      Disjoint K (closure Q.inside ∪ (D2 \ P.inside)) := by
  rcases h with ⟨hi, _⟩ | ⟨ho, _⟩ | ⟨_, hd⟩
  · exact Or.inl (fun x hx ↦ Or.inl (subset_closure (hi hx)))
  · exact Or.inl (fun x hx ↦ Or.inr ⟨(ho hx).1, fun hp ↦ (ho hx).2 (subset_closure hp)⟩)
  · exact Or.inr hd

theorem disjoint_circle_component_location {m n : ℕ}
    (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (hdisj : Disjoint (closure P.inside) (closure Q.inside))
    {K : Set V2} (hK : IsPreconnected K) (hKD : K ⊆ D2)
    (hKP : Disjoint K (P.boundary ℝ)) (hKQ : Disjoint K (Q.boundary ℝ)) :
    DisjointCircleComponentLocation P Q K := by
  obtain ⟨_, hiP, hfP, _⟩ := polygon_source_region P
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hP hinjP (convex_ball _ _) hPsq
  obtain ⟨_, hiQ, hfQ, _⟩ := polygon_source_region Q
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) hQ hinjQ (convex_ball _ _) hQsq
  have hsideP := component_sides_of_disjoint_frontier hK isClosed_closure (hfP ▸ hKP)
  have hsideQ := component_sides_of_disjoint_frontier hK isClosed_closure (hfQ ▸ hKQ)
  rw [hiP] at hsideP
  rw [hiQ] at hsideQ
  rcases hsideP with hPin | hPout
  · refine Or.inl ⟨hPin, hdisj.mono_left (hPin.trans subset_closure), ?_⟩
    exact disjoint_left.mpr (fun x hx ho ↦ ho.2 (Or.inl (hPin hx)))
  · rcases hsideQ with hQin | hQout
    · refine Or.inr (Or.inl ⟨hQin, hdisj.symm.mono_left (hQin.trans subset_closure), ?_⟩)
      exact disjoint_left.mpr (fun x hx ho ↦ ho.2 (Or.inr (hQin hx)))
    · exact Or.inr (Or.inr (fun x hx ↦
        ⟨hKD hx, fun h ↦ h.elim (hPout hx) (hQout hx)⟩))

theorem DisjointCircleComponentLocation.retained_piece {m n : ℕ}
    {P : Polygon V2 (m + 3)} {Q : Polygon V2 (n + 3)} {K : Set V2}
    (h : DisjointCircleComponentLocation P Q K) :
    K ⊆ closure P.inside ∨ K ⊆ closure Q.inside ∨ K ⊆ D2 \ (P.inside ∪ Q.inside) := by
  rcases h with ⟨hP, _, _⟩ | ⟨hQ, _, _⟩ | ho
  · exact Or.inl (hP.trans subset_closure)
  · exact Or.inr (Or.inl (hQ.trans subset_closure))
  · exact Or.inr (Or.inr (fun x hx ↦ ⟨(ho hx).1, fun h ↦
      (ho hx).2 (h.elim (fun hp ↦ Or.inl (subset_closure hp))
        (fun hq ↦ Or.inr (subset_closure hq)))⟩))

theorem old_circle_component_source_cases
    {X I : Type*} {f : V2 → X} (U : I → Set V2) (a b : I) (hab : a ≠ b)
    (hcover : ⋃ i, U i = PoincareConjecture.M76.Dehn.doubleLocusOn f D2)
    (hconn : ∀ i, IsConnected (U i))
    (hpairwise : Pairwise (fun i k ↦ Disjoint (U i) (U k)))
    {m n : ℕ} (P : Polygon V2 (m + 3)) (Q : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (hPsq : P.boundary ℝ ⊆ ball 0 1) (hQsq : Q.boundary ℝ ⊆ ball 0 1)
    (ha : U a = P.boundary ℝ) (hb : U b = Q.boundary ℝ) :
    (closure Q.inside ⊆ P.inside ∧
      ∀ i, i ≠ a → i ≠ b → NestedCircleComponentLocation P Q (U i)) ∨
    (closure P.inside ⊆ Q.inside ∧
      ∀ i, i ≠ a → i ≠ b → NestedCircleComponentLocation Q P (U i)) ∨
    (Disjoint (closure P.inside) (closure Q.inside) ∧
      ∀ i, i ≠ a → i ≠ b → DisjointCircleComponentLocation P Q (U i)) := by
  have hUD (i : I) : U i ⊆ D2 := by
    intro x hx
    exact (hcover.subset (mem_iUnion.mpr ⟨i, hx⟩)).1
  have hboundary : Disjoint (P.boundary ℝ) (Q.boundary ℝ) := by
    rw [← ha, ← hb]
    exact hpairwise hab
  obtain ⟨_, _, hiP, hiQ, _, _, _, _, hcases⟩ :=
    interior_polygon_source_regions P Q hP hinjP hQ hinjQ hboundary hPsq hQsq
  rw [hiP, hiQ] at hcases
  have havoid (i : I) (hia : i ≠ a) (hib : i ≠ b) :
      Disjoint (U i) (P.boundary ℝ) ∧ Disjoint (U i) (Q.boundary ℝ) := by
    rw [← ha, ← hb]
    exact ⟨hpairwise hia, hpairwise hib⟩
  rcases hcases with hPQ | hQP | hd
  · refine Or.inr (Or.inl ⟨hPQ, ?_⟩)
    intro i hia hib
    exact nested_circle_component_location Q P hQ hinjQ hP hinjP hQsq hPsq hPQ
      (hconn i).isPreconnected (hUD i) (havoid i hia hib).2 (havoid i hia hib).1
  · refine Or.inl ⟨hQP, ?_⟩
    intro i hia hib
    exact nested_circle_component_location P Q hP hinjP hQ hinjQ hPsq hQsq hQP
      (hconn i).isPreconnected (hUD i) (havoid i hia hib).1 (havoid i hia hib).2
  · refine Or.inr (Or.inr ⟨hd, ?_⟩)
    intro i hia hib
    exact disjoint_circle_component_location P Q hP hinjP hQ hinjQ hPsq hQsq hd
      (hconn i).isPreconnected (hUD i) (havoid i hia hib).1 (havoid i hia hib).2

end Dehn
