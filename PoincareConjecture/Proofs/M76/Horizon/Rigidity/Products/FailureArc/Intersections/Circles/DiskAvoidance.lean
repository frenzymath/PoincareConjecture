import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.SpanningArcDisk



set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem disjoint_polygon_disk_of_connected_set
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    {A : Set P2} (hA : IsPreconnected A) (hdis : Disjoint A (P.boundary ℝ))
    (hout : ∃ x ∈ A, x ∉ closure P.inside) :
    Disjoint A (closure P.inside) := by
  have hsides : A ⊆ P.inside ∨ A ⊆ P.outside := by
    apply hA.subset_or_subset (P.isOpen_inside hP hi) (P.isOpen_outside hP hi)
      P.disjoint_inside_outside
    rw [← P.compl_boundary_eq_inside_union_outside]
    exact fun x hx hp => Set.disjoint_left.mp hdis hx hp
  rcases hsides with hin | houtside
  · obtain ⟨x, hx, hxn⟩ := hout
    exact (hxn (subset_closure (hin hx))).elim
  · apply Set.disjoint_left.mpr
    intro x hx hp
    rw [P.closure_inside hP hi] at hp
    exact hp (houtside hx)

theorem disjoint_polygon_disk_of_spanning_set
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    {L d : ℝ}
    (hboundary : ∀ x ∈ P.boundary ℝ, -d < depth L x ∧ depth L x < d)
    {A : Set P2} (hA : IsPreconnected A) (hdis : Disjoint A (P.boundary ℝ))
    (houter : ∃ x ∈ A, depth L x = -d) :
    Disjoint A (closure P.inside) := by
  apply disjoint_polygon_disk_of_connected_set P hP hi hA hdis
  obtain ⟨x, hx, hd⟩ := houter
  refine ⟨x, hx, ?_⟩
  intro hp
  have hh := (mem_interior_annulusSquare_iff L (-d) x).mp
    ((source_polygon_disk_or_enclosing P hP hi hboundary).2.1 hp)
  exact lt_irrefl (-d) (hd ▸ hh)

end PoincareConjecture.M76.Dehn.Annuli
