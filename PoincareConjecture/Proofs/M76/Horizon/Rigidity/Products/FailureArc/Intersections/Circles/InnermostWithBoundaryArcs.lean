import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.DiskAvoidance
import PoincareConjecture.Proofs.M76.Mathlib.InnermostPolygonDisk

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Rim" => Set.ofPred (fun x : P2 => depth 8 x = -1 ∨ depth 8 x = 1)

theorem exists_innermost_circle_avoiding_boundary_arcs
    {κ α : Type*} [Finite κ] [Nonempty κ]
    (n : κ → ℕ) (P : ∀ i, Polygon P2 (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    (hboundary : ∀ i x, x ∈ (P i).boundary ℝ → -1 < depth 8 x ∧ depth 8 x < 1)
    (hdis : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)))
    {A : Set P2} (hA : IsPreconnected A)
    (hAP : ∀ i, Disjoint A ((P i).boundary ℝ))
    (houter : ∃ x ∈ A, depth 8 x = -1) (hinner : ∃ x ∈ A, depth 8 x = 1)
    (arcs : α → Set P2) (hconn : ∀ a, IsPreconnected (arcs a))
    (hrim : ∀ a, (arcs a ∩ Rim).Nonempty)
    (harcs : ∀ a i, Disjoint (arcs a) ((P i).boundary ℝ)) :
    ∃ i, IsFinitePLBallPair P2 (closure (P i).inside) ((P i).boundary ℝ) ∧
      closure (P i).inside ⊆ {x : P2 | -1 < depth 8 x ∧ depth 8 x < 1} ∧
      Disjoint A (closure (P i).inside) ∧
      Disjoint (⋃ a, arcs a) (closure (P i).inside) ∧
      closure (P i).inside ∩ ((⋃ a, arcs a) ∪ (⋃ j, (P j).boundary ℝ)) =
        (P i).boundary ℝ ∧
      Disjoint (P i).inside ((⋃ a, arcs a) ∪ (⋃ j, (P j).boundary ℝ)) := by
  obtain ⟨i, hball, hinter, havoid⟩ :=
    Polygon.exists_innermost_finitePL_disk n P hP hPi hdis
  have hinside := (polygon_disk_of_disjoint_spanning_set (P i) (hP i) (hPi i)
    (hboundary i) hA (hAP i) houter hinner).2
  have hAavoid := disjoint_polygon_disk_of_spanning_set (P i) (hP i) (hPi i)
    (hboundary i) hA (hAP i) houter
  have hfull : Disjoint (⋃ a, arcs a) (closure (P i).inside) := by
    apply disjoint_iUnion_left.mpr
    intro a
    apply disjoint_polygon_disk_of_connected_set (P i) (hP i) (hPi i) (hconn a) (harcs a i)
    obtain ⟨x, hxa, hxrim⟩ := hrim a
    refine ⟨x, hxa, ?_⟩
    intro hxD
    have hx := hinside hxD
    rcases hxrim with h | h <;> linarith [hx.1, hx.2]
  refine ⟨i, hball, hinside, hAavoid, hfull, ?_, ?_⟩
  · rw [inter_union_distrib_left, hfull.symm.inter_eq, empty_union, hinter]
  · exact disjoint_union_right.mpr
      ⟨hfull.symm.mono_left subset_closure, havoid⟩

end PoincareConjecture.M76.Dehn.Annuli
