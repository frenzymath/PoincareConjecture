import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.SourceCircleCuts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_enclosing_polygon_complementary_annuli {n : ℕ}
    (P : Polygon P2 (n + 3)) (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    {L d : ℝ} (hd : 0 < d) (hwidth : 2 * d < L)
    (hboundary : ∀ p ∈ P.boundary ℝ, -d < depth L p ∧ depth L p < d)
    (henclosing : annulusSquare L d ⊆ P.inside) :
    ∃ (outer : Ann ≃ₜ (annulusSquare L (-d) \ P.inside : Set P2))
      (inner : Ann ≃ₜ (closure P.inside \ interior (annulusSquare L d) : Set P2)),
      outer.IsFinitePL ∧ inner.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ depth L (outer z : P2) = -d) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (outer z : P2) ∈ P.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (inner z : P2) ∈ P.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ depth L (inner z : P2) = d) ∧
      (annulusSquare L (-d) \ P.inside) ∪
        (closure P.inside \ interior (annulusSquare L d)) = squareAnnulus L d ∧
      (annulusSquare L (-d) \ P.inside) ∩
        (closure P.inside \ interior (annulusSquare L d)) = P.boundary ℝ := by
  have houter := (source_polygon_disk_or_enclosing P hP hi hboundary).2.1
  have hp : IsFinitePLBallPair P2 (closure P.inside) (frontier (closure P.inside)) := by
    rw [P.frontier_closure_inside hP hi]
    exact P.isFinitePLBallPair_closed_inside hP hi
  have hinner : annulusSquare L d ⊆ interior (closure P.inside) := by
    rwa [P.interior_closure_inside hP hi]
  have hout := exists_square_annulus_nested_disks hp
    (isFinitePLBallPair_annulusSquare (L := L) (u := -d) (by linarith))
    houter (L := 8) (d := 1) (by norm_num) (by norm_num)
  rw [P.interior_closure_inside hP hi] at hout
  obtain ⟨outer, houterPL, hoo, hoi⟩ := hout
  obtain ⟨inner, hinnerPL, hio, hii⟩ := exists_square_annulus_nested_disks
    (isFinitePLBallPair_annulusSquare hwidth) hp hinner
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  refine ⟨outer, inner, houterPL, hinnerPL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact (hoo z).trans (mem_frontier_annulusSquare_iff L (-d) _)
  · intro z
    simpa only [P.frontier_closure_inside hP hi] using hoi z
  · intro z
    simpa only [P.frontier_closure_inside hP hi] using hio z
  · intro z
    exact (hii z).trans (mem_frontier_annulusSquare_iff L d _)
  · ext p
    constructor
    · rintro (hp | hp)
      · apply mem_squareAnnulus_iff_depth.mpr
        refine ⟨(mem_annulusSquare_iff L (-d) p).mp hp.1, ?_⟩
        exact (lt_of_not_ge (fun h ↦ hp.2 (henclosing
          ((mem_annulusSquare_iff L d p).mpr h)))).le
      · apply mem_squareAnnulus_iff_depth.mpr
        refine ⟨((mem_interior_annulusSquare_iff L (-d) p).mp (houter hp.1)).le, ?_⟩
        exact le_of_not_gt (fun h ↦ hp.2 ((mem_interior_annulusSquare_iff L d p).mpr h))
    · intro hp
      have hh := mem_squareAnnulus_iff_depth.mp hp
      by_cases hin : p ∈ P.inside
      · exact Or.inr ⟨subset_closure hin, fun h ↦ (not_lt_of_ge hh.2)
          ((mem_interior_annulusSquare_iff L d p).mp h)⟩
      · exact Or.inl ⟨(mem_annulusSquare_iff L (-d) p).mpr hh.1, hin⟩
  · ext p
    constructor
    · rintro ⟨hp, hq⟩
      rw [← P.frontier_inside hP hi, frontier, (P.isOpen_inside hP hi).interior_eq]
      exact ⟨hq.1, hp.2⟩
    · intro hp
      have hpcl : p ∈ closure P.inside := by
        rw [← P.frontier_inside hP hi] at hp
        exact frontier_subset_closure hp
      have hpnot : p ∉ P.inside := by
        have hh := hp
        rw [← P.frontier_inside hP hi, frontier,
          (P.isOpen_inside hP hi).interior_eq] at hh
        exact hh.2
      refine ⟨⟨interior_subset (houter hpcl), hpnot⟩, hpcl, ?_⟩
      intro hin
      exact hpnot (henclosing (interior_subset hin))

end PoincareConjecture.M76.Dehn.Annuli
