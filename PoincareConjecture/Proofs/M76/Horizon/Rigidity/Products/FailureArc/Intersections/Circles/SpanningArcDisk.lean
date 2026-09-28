import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.SourceCircleCuts

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem polygon_disk_of_disjoint_spanning_set
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    {L d : ℝ}
    (hboundary : ∀ x ∈ P.boundary ℝ, -d < depth L x ∧ depth L x < d)
    {A : Set P2} (hA : IsPreconnected A)
    (hdis : Disjoint A (P.boundary ℝ))
    (houter : ∃ x ∈ A, depth L x = -d)
    (hinner : ∃ x ∈ A, depth L x = d) :
    IsFinitePLBallPair P2 (closure P.inside) (P.boundary ℝ) ∧
      closure P.inside ⊆ {x : P2 | -d < depth L x ∧ depth L x < d} := by
  obtain ⟨hball, hout, henclosing | hinside⟩ := source_polygon_disk_or_enclosing P hP hi hboundary
  · have hsides : A ⊆ P.inside ∨ A ⊆ P.outside := by
      apply hA.subset_or_subset (P.isOpen_inside hP hi) (P.isOpen_outside hP hi)
        P.disjoint_inside_outside
      rw [← P.compl_boundary_eq_inside_union_outside]
      exact fun x hx hp => Set.disjoint_left.mp hdis hx hp
    rcases hsides with hinside | houtside
    · obtain ⟨x, hx, hd⟩ := houter
      have hh := (mem_interior_annulusSquare_iff L (-d) x).mp
        (hout (subset_closure (hinside hx)))
      exact (lt_irrefl (-d) (hd ▸ hh)).elim
    · obtain ⟨x, hx, hd⟩ := hinner
      exact (Set.disjoint_left.mp P.disjoint_inside_outside
        (henclosing ((mem_annulusSquare_iff L d x).mpr hd.ge)) (houtside hx)).elim
  · exact ⟨hball, hinside⟩

end PoincareConjecture.M76.Dehn.Annuli
