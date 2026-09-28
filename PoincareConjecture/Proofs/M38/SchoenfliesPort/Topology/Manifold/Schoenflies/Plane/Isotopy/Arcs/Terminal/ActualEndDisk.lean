import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.UpperGeometry
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ConnectedMiddle
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutCircles

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel SphereSurgeryCoreCap Poincare.Geometry.Euclidean
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem lower_endpoint_disk
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b) (haD : a ≤ D.center) (hDb : D.center < b)
    (p : S2) (hp : b < inner Real v (g p)) :
    ∃ m : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target ∧
      m '' closedBall 0 1 = A.cappedRegion b ∧
      m '' sphere (0 : E2) 1 = range (fun q : S1 => A.chart (q, b)) := by
  obtain ⟨hf, hi, hd⟩ := A.slice_geometry haD ⟨hDb.le, le_rfl⟩
  have hproper : A.cappedRegion b ≠ univ := by
    intro heq
    have hh := A.height_le_cut_of_mem_cappedRegion hDb.le le_rfl
      (heq.symm ▸ mem_univ p)
    exact (not_le_of_gt hp) hh
  have hne : (_root_.interior (A.cappedRegion b) \
      range (fun q : S1 => A.chart (q, b))).Nonempty := by
    have hpD : D.chart 0 ∈ D.chart '' closedBall (0 : E2) 1 :=
      mem_image_of_mem _ (mem_closedBall_self zero_le_one)
    refine ⟨D.chart 0, A.cap_subset_interior_cappedRegion haD hDb le_rfl hpD, ?_⟩
    rintro ⟨q, hq⟩
    have hh := A.height_le_center_of_mem_cap hpD
    rw [← hq, A.actual_height q b ⟨hDb.le, le_rfl⟩] at hh
    exact (not_le_of_gt hDb) hh
  exact exists_disk_neighborhood_of_frontier_subset_circle hf hi hd
    (A.isCompact_cappedRegion haD le_rfl).isClosed hproper
    (A.frontier_cappedRegion_subset_terminal haD hDb le_rfl) hne

private theorem upper_endpoint_disk
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : UpperAnnularEnd D C h a b) (hDb : D.center ≤ b) (haD : a < D.center)
    (p : S2) (hp : inner Real v (g p) < a) :
    ∃ m : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target ∧
      m '' closedBall 0 1 = A.cappedRegion a ∧
      m '' sphere (0 : E2) 1 = range (fun q : S1 => A.chart (q, a)) := by
  have hp' : -a < inner Real v (heightReflection D.unit_v (g p)) := by
    rw [inner_heightReflection]
    exact neg_lt_neg hp
  obtain ⟨m, hms, hm, hmi, hmc, hmb⟩ := lower_endpoint_disk A.reflected
    (neg_le_neg hDb) (neg_lt_neg haD) p hp'
  refine ⟨m, hms, hm, hmi, hmc.trans (A.cappedRegion_eq_reflected a).symm, ?_⟩
  simpa only [UpperAnnularEnd.chart_apply] using hmb

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

set_option maxHeartbeats 400000 in

theorem exists_terminal_actual_end_disk
    (d : TerminalSaddleGeometry M P p e) (i : d.ends.EndIndex) :
    ∃ m : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target ∧
      m '' closedBall 0 1 = terminalEndCap d.ends i ∧
      m '' sphere (0 : E2) 1 =
        match i with
        | .inl j => range (d.ends.lowerCutCircle j)
        | .inr j => range (d.ends.upperCutCircle j) := by
  rcases i with i | i
  · let A := d.ends.lower i.1.1 i.1.2 i.2
    have hp : d.ends.lowerCut < inner Real (M.v : E3) (g p) := by
      rw [d.lowerCut_eq]
      linarith [d.eta_pos]
    obtain ⟨m, hms, hm, hmi, hmc, hmb⟩ := lower_endpoint_disk A
      (d.ends.cap_center_bounds i.1.1 i.1.2).1.le i.2 p hp
    refine ⟨m, hms, hm, hmi, ?_, hmb⟩
    change m '' closedBall (0 : E2) 1 = A.region ∪ i.1.1.chart '' closedBall (0 : E2) 1
    exact hmc.trans (union_comm (i.1.1.chart '' closedBall (0 : E2) 1) A.region)
  · let A := d.ends.upper i.1.1 i.1.2 i.2
    have hp : inner Real (M.v : E3) (g p) < d.ends.upperCut := by
      rw [d.upperCut_eq]
      linarith [d.eta_pos]
    obtain ⟨m, hms, hm, hmi, hmc, hmb⟩ := upper_endpoint_disk
      (v := (M.v : E3)) (g := g) (D := i.1.1) (C := P.core)
      (h := d.ends.height) (a := d.ends.upperCut) (b := d.ends.upperBound) A
      (d.ends.cap_center_bounds i.1.1 i.1.2).2.le i.2 p hp
    refine ⟨m, hms, hm, hmi, ?_, hmb⟩
    change m '' closedBall (0 : E2) 1 = A.region ∪ i.1.1.chart '' closedBall (0 : E2) 1
    rw [A.region_eq_image]
    exact hmc.trans (union_comm (i.1.1.chart '' closedBall (0 : E2) 1)
      (A.chart '' (univ ×ˢ Icc d.ends.upperCut i.1.1.center)))

theorem exists_terminal_actual_end_disks
    (d : TerminalSaddleGeometry M P p e) :
    ∃ m : Fin 3 → OpenPartialHomeomorph E2 S2, ∀ i,
      closedBall 0 1 ⊆ (m i).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ (m i) (m i).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ (m i).symm (m i).target ∧
      m i '' closedBall 0 1 = terminalEndCap d.ends (d.labels i) ∧
      m i '' sphere (0 : E2) 1 =
        match d.labels i with
        | .inl j => range (d.ends.lowerCutCircle j)
        | .inr j => range (d.ends.upperCutCircle j) := by
  choose m hm using fun i => exists_terminal_actual_end_disk d (d.labels i)
  exact ⟨m, hm⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
