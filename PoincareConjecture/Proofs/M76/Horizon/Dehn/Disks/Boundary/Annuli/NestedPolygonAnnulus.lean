import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedShellHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_square_annulus_nested_disks {S T : Set P2} {L d : ℝ}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (hd : 0 < d) (hwidth : 2 * d < L) :
    ∃ H : squareAnnulus L d ≃ₜ (T \ interior S : Set P2), H.IsFinitePL ∧
      (∀ z : squareAnnulus L d, depth L (z : P2) = -d ↔ (H z : P2) ∈ frontier T) ∧
      (∀ z : squareAnnulus L d, depth L (z : P2) = d ↔ (H z : P2) ∈ frontier S) := by
  have houter := Dehn.isFinitePLBallPair_annulusSquare (show 2 * (-d) < L by linarith)
  have hinner := Dehn.isFinitePLBallPair_annulusSquare hwidth
  have hsub : Dehn.annulusSquare L d ⊆ interior (Dehn.annulusSquare L (-d)) := by
    intro z hz
    rw [Dehn.mem_annulusSquare_iff] at hz
    rw [Dehn.mem_interior_annulusSquare_iff]
    linarith
  have heq : Dehn.annulusSquare L (-d) \ interior (Dehn.annulusSquare L d) =
      squareAnnulus L d := by
    ext z
    rw [mem_sdiff, Dehn.mem_annulusSquare_iff, Dehn.mem_interior_annulusSquare_iff,
      mem_squareAnnulus_iff_depth, mem_Icc]
    exact and_congr_right (fun _ ↦ not_lt)
  obtain ⟨H, hH, ho, hi⟩ := exists_nested_shell_homeomorph hinner houter hsub hS hT hST
  let G := (Homeomorph.setCongr heq.symm).trans
    (H.trans (Homeomorph.setCongr (rfl : T \ interior S = T \ interior S)))
  refine ⟨G, hH.setCongr heq rfl, ?_, ?_⟩
  · intro z
    exact (Dehn.mem_frontier_annulusSquare_iff L (-d) z).symm.trans (ho ⟨z, heq.symm ▸ z.property⟩)
  · intro z
    exact (Dehn.mem_frontier_annulusSquare_iff L d z).symm.trans (hi ⟨z, heq.symm ▸ z.property⟩)

theorem exists_square_annulus_nested_polygons {m n : ℕ}
    (P : Polygon P2 (m + 3)) (Q : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    (hnest : closure Q.inside ⊆ P.inside) {L d : ℝ}
    (hd : 0 < d) (hwidth : 2 * d < L) :
    ∃ H : squareAnnulus L d ≃ₜ (closure P.inside \ Q.inside : Set P2), H.IsFinitePL ∧
      (∀ z : squareAnnulus L d, depth L (z : P2) = -d ↔ (H z : P2) ∈ P.boundary ℝ) ∧
      (∀ z : squareAnnulus L d, depth L (z : P2) = d ↔ (H z : P2) ∈ Q.boundary ℝ) := by
  have hp : IsFinitePLBallPair P2 (closure P.inside) (frontier (closure P.inside)) := by
    rw [P.frontier_closure_inside hP hPi]
    exact P.isFinitePLBallPair_closed_inside hP hPi
  have hq : IsFinitePLBallPair P2 (closure Q.inside) (frontier (closure Q.inside)) := by
    rw [Q.frontier_closure_inside hQ hQi]
    exact Q.isFinitePLBallPair_closed_inside hQ hQi
  have hs : closure Q.inside ⊆ interior (closure P.inside) := by
    rwa [P.interior_closure_inside hP hPi]
  obtain ⟨H, hH, ho, hi⟩ := exists_square_annulus_nested_disks hq hp hs hd hwidth
  have heq : closure P.inside \ interior (closure Q.inside) = closure P.inside \ Q.inside := by
    rw [Q.interior_closure_inside hQ hQi]
  let G := (Homeomorph.setCongr (rfl : squareAnnulus L d = squareAnnulus L d)).trans
    (H.trans (Homeomorph.setCongr heq))
  refine ⟨G, hH.setCongr rfl heq, ?_, ?_⟩
  · intro z
    change depth L (z : P2) = -d ↔ (H z : P2) ∈ P.boundary ℝ
    simpa only [P.frontier_closure_inside hP hPi] using ho z
  · intro z
    change depth L (z : P2) = d ↔ (H z : P2) ∈ Q.boundary ℝ
    simpa only [Q.frontier_closure_inside hQ hQi] using hi z

end PoincareConjecture.M76.Dehn
