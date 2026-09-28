import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.EssentialSquareAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceRegions

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)



theorem source_polygon_disk_or_enclosing {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P) {L d : ℝ}
    (hboundary : ∀ p ∈ P.boundary ℝ, -d < depth L p ∧ depth L p < d) :
    IsFinitePLBallPair P2 (closure P.inside) (P.boundary ℝ) ∧
      closure P.inside ⊆ interior (annulusSquare L (-d)) ∧
      (annulusSquare L d ⊆ P.inside ∨
        closure P.inside ⊆ {p : P2 | -d < depth L p ∧ depth L p < d}) := by
  have hcv : Convex ℝ (annulusSquare L (-d)) := (convex_Icc _ _).prod (convex_Icc _ _)
  have houter : closure P.inside ⊆ interior (annulusSquare L (-d)) :=
    P.closure_inside_subset_convex hP hi hcv.interior (by
      rintro p ⟨i, rfl⟩
      exact (mem_interior_annulusSquare_iff L (-d) _).mpr
        (hboundary _ (P.vertex_mem_boundary i)).1)
  refine ⟨P.isFinitePLBallPair_closed_inside hP hi, houter, ?_⟩
  have hinner : Convex ℝ (annulusSquare L d) := (convex_Icc _ _).prod (convex_Icc _ _)
  have hside : annulusSquare L d ⊆ P.inside ∨ annulusSquare L d ⊆ P.outside := by
    apply hinner.isPreconnected.subset_or_subset
      (P.isOpen_inside hP hi) (P.isOpen_outside hP hi) P.disjoint_inside_outside
    rw [← P.compl_boundary_eq_inside_union_outside]
    intro p hp hpb
    exact (not_lt_of_ge ((mem_annulusSquare_iff L d p).mp hp)) (hboundary p hpb).2
  rcases hside with hin | hout
  · exact Or.inl hin
  · refine Or.inr fun p hp ↦ ⟨(mem_interior_annulusSquare_iff L (-d) p).mp (houter hp), ?_⟩
    apply lt_of_not_ge
    intro hge
    have ho := hout ((mem_annulusSquare_iff L d p).mpr hge)
    rw [P.closure_inside hP hi] at hp
    exact hp ho



theorem enclosing_source_polygons_nested {m n : ℕ}
    (P : Polygon P2 (m + 3)) (Q : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hiP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hiQ : Function.Injective Q)
    (hdis : Disjoint (P.boundary ℝ) (Q.boundary ℝ)) {L d : ℝ}
    (hwidth : 2 * d < L) (hPin : annulusSquare L d ⊆ P.inside)
    (hQin : annulusSquare L d ⊆ Q.inside) :
    closure P.inside ⊆ Q.inside ∨ closure Q.inside ⊆ P.inside := by
  rcases P.closed_inside_nested_or_disjoint Q hP hiP hQ hiQ hdis with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hpoint : (d, d) ∈ annulusSquare L d := by
      change (d ≤ d ∧ d ≤ L - d) ∧ (d ≤ d ∧ d ≤ L - d)
      constructor <;> exact ⟨le_rfl, by linarith⟩
    exact (Set.disjoint_left.mp h (subset_closure (hPin hpoint))
      (subset_closure (hQin hpoint))).elim

end PoincareConjecture.M76.Dehn.Annuli
