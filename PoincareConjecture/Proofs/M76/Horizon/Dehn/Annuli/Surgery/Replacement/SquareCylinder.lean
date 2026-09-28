import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.SquareCylinder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Cyl" => Set.prod (sphere (0 : V2) 1) (Icc (-1 : ℝ) 1)



theorem exists_square_annulus_cylinder_chart {L d : ℝ}
    (hd : 0 < d) (hwidth : 2 * d < L) :
    ∃ H : Cyl ≃ₜ squareAnnulus L d, H.IsFinitePL ∧
      (∀ z : Cyl, (z : V2 × ℝ).2 = -1 ↔ depth L (H z : P2) = -d) ∧
      (∀ z : Cyl, (z : V2 × ℝ).2 = 1 ↔ depth L (H z : P2) = d) := by
  have hsub : annulusSquare L d ⊆ interior (annulusSquare L (-d)) := by
    intro p hp
    rw [mem_interior_annulusSquare_iff]
    have hh := (mem_annulusSquare_iff L d p).mp hp
    linarith
  have hset : annulusSquare L (-d) \ interior (annulusSquare L d) =
      squareAnnulus L d := by
    ext p
    rw [mem_sdiff, mem_annulusSquare_iff, mem_interior_annulusSquare_iff,
      mem_squareAnnulus_iff_depth, mem_Icc]
    exact and_congr_right (fun _ ↦ not_lt)
  obtain ⟨A, hA, hAo, hAi⟩ := exists_square_annulus_nested_disks
    (isFinitePLBallPair_annulusSquare hwidth)
    (isFinitePLBallPair_annulusSquare (L := L) (u := -d) (by linarith))
    hsub (L := 8) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨C, hC, hCv⟩ := exists_selected_annulus_cylinder
  let H := C.symm.trans (A.trans (Homeomorph.setCongr hset))
  have hheight (z : Cyl) : (z : V2 × ℝ).2 = depth 8 (C.symm z : P2) := by
    simpa only [C.apply_symm_apply] using hCv (C.symm z)
  refine ⟨H, hC.symm.trans (hA.setCongr rfl hset), ?_, ?_⟩
  · intro z
    rw [hheight]
    exact (hAo (C.symm z)).trans (mem_frontier_annulusSquare_iff L (-d) _)
  · intro z
    rw [hheight]
    exact (hAi (C.symm z)).trans (mem_frontier_annulusSquare_iff L d _)

end PoincareConjecture.M76.Dehn.Annuli
