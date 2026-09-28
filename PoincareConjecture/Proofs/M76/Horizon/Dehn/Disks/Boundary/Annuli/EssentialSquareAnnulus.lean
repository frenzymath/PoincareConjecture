import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.EssentialPolygonNesting
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares











set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open _root_.Dehn
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1



theorem essential_polygon_in_square_annulus
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) {L d : ℝ}
    (hboundary : ∀ p ∈ P.boundary ℝ, -d < depth L p ∧ depth L p < d)
    (gamma : C(Q2, squareAnnulus L d))
    (hgamma : ∀ x, (gamma x : P2) ∈ P.boundary ℝ)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    annulusSquare L d ⊆ P.inside ∧
      closure P.inside ⊆ interior (annulusSquare L (-d)) := by
  have hcv : Convex ℝ (annulusSquare L (-d)) := (convex_Icc _ _).prod (convex_Icc _ _)
  have houter : closure P.inside ⊆ interior (annulusSquare L (-d)) :=
    P.closure_inside_subset_convex hP hinj hcv.interior (by
      rintro p ⟨i, rfl⟩
      exact (mem_interior_annulusSquare_iff L (-d) _).mpr
        (hboundary _ (P.vertex_mem_boundary i)).1)
  have hinnerCv : Convex ℝ (annulusSquare L d) := (convex_Icc _ _).prod (convex_Icc _ _)
  have hside : annulusSquare L d ⊆ P.inside ∨ annulusSquare L d ⊆ P.outside := by
    apply hinnerCv.isPreconnected.subset_or_subset
      (P.isOpen_inside hP hinj) (P.isOpen_outside hP hinj) P.disjoint_inside_outside
    rw [← P.compl_boundary_eq_inside_union_outside]
    intro p hp hpb
    have hge := (mem_annulusSquare_iff L d p).mp hp
    exact (not_lt_of_ge hge) (hboundary p hpb).2
  rcases hside with hinner | hout
  · exact ⟨hinner, houter⟩
  · have hcontained : closure P.inside ⊆ squareAnnulus L d := by
      intro p hp
      have hpout := (mem_interior_annulusSquare_iff L (-d) p).mp (houter hp)
      have hpnot : p ∉ annulusSquare L d := by
        intro hpinner
        have hpo := hout hpinner
        rw [P.closure_inside hP hinj] at hp
        exact hp hpo
      have hpdepth : depth L p < d := lt_of_not_ge (fun h ↦
        hpnot ((mem_annulusSquare_iff L d p).mpr h))
      exact mem_squareAnnulus_iff_depth.mpr ⟨hpout.le, hpdepth.le⟩
    have hb : P.boundary ℝ ⊆ closure P.inside := by
      rw [← P.frontier_inside hP hinj]
      exact frontier_subset_closure
    exact (hessential (squareRimLoop_class_eq_one_of_polygon_disk P hP hinj hcontained
      gamma (fun x ↦ hb (hgamma x)))).elim

end PoincareConjecture.M76.Dehn
