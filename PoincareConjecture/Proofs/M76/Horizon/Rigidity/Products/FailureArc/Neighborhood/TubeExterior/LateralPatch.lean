import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.SourceBox
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares
import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalSegments
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_lateral_disk_patch {r : ℝ} (hr : 0 < r)
    {z : C3} (hz : z ∈ lateral r) :
    ∃ P Q V : Set C3,
      IsFinitePLBallPair P2 P Q ∧ P ⊆ lateral r ∧ IsOpen V ∧ z ∈ V ∧
      (∀ w ∈ V, w ∈ lateral r ↔ w ∈ P) ∧
      (∀ w ∈ P, w ∈ V → (w ∈ Q ↔ w.2 = 0 ∨ w.2 = 1)) := by
  obtain ⟨n, B, hB, hBi, hBd⟩ :=
    _root_.Dehn.exists_polygon_annulusSquare_frontier (L := 0) (u := -r) (by linarith)
  have hsq : _root_.Dehn.annulusSquare 0 (-r) = transverseSquare r := by
    simp only [_root_.Dehn.annulusSquare, transverseSquare, zero_sub, neg_neg]
  rw [hsq] at hBd
  obtain ⟨u, v, hu, hv, huv, hsub, hlocal⟩ :=
    B.exists_local_segment_pair hB hBi (hBd.symm.subset hz.1)
  let A := segment ℝ z.1 u ∪ segment ℝ z.1 v
  have hA : IsFinitePLBallPair ℝ A {u, v} := by
    have hp := isFinitePLBallPair_two_segments hu hv.symm (by
      simpa only [segment_symm ℝ u z.1] using huv)
    simpa only [A, segment_symm ℝ u z.1] using hp
  have hArim : A ⊆ frontier (transverseSquare r) := hsub.trans hBd.subset
  obtain ⟨O, hOsub, hO, hzO⟩ := mem_nhds_iff.mp hlocal
  let V := (O \ ({u, v} : Set P2)) ×ˢ (univ : Set ℝ)
  have hV : IsOpen V := (hO.sdiff ((finite_singleton v).insert u).isClosed).prod
    isOpen_univ
  have hzV : z ∈ V := by
    refine ⟨⟨hzO, ?_⟩, mem_univ _⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    exact not_or.mpr ⟨hu.symm, hv.symm⟩
  refine ⟨A ×ˢ Icc 0 1, ({u, v} ×ˢ Icc 0 1) ∪ (A ×ˢ {0, 1}), V,
    hA.prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)),
    prod_mono hArim Subset.rfl, hV, hzV, ?_, ?_⟩
  · intro w hw
    change (w.1 ∈ frontier (transverseSquare r) ∧ w.2 ∈ Icc 0 1) ↔ _
    rw [← hBd]
    exact and_congr_left (fun _ => hOsub hw.1.1)
  · intro w hw hwV
    change ((w.1 ∈ ({u, v} : Set P2) ∧ w.2 ∈ Icc 0 1) ∨
      (w.1 ∈ A ∧ (w.2 = 0 ∨ w.2 = 1))) ↔ _
    simp only [hwV.1.2, false_and, false_or, hw.1, true_and]

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
