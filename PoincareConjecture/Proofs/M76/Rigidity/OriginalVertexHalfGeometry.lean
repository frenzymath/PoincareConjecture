import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexHalfBlocks
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBase

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem vertex_half_ballPair_and_outside (p : (T.marked 2).vertices)
    (w : ℝ) (hw : w ≠ 0) :
    let Z : Set (T.index → ℝ × V3) :=
      {x | 0 ≤ w * (T.chart (T.chart_index p) (T.inverse x)).2}
    IsFinitePLBallPair C3 (T.dualRegion {(p : T.index → ℝ × V3)} ∩ Z)
      ((T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ Z) ∪
        T.diskDualBase {(p : T.index → ℝ × V3)}) ∧
      (((T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ Z) ∪
          T.diskDualBase {(p : T.index → ℝ × V3)}) \
        T.diskDualBase {(p : T.index → ℝ × V3)}).Nonempty := by
  classical
  let N := T.vertexBlock p
  let Z : Set (T.index → ℝ × V3) :=
    {x | 0 ≤ w * (T.chart (T.chart_index p) (T.inverse x)).2}
  let O := ((N.link p).space ∩ (T.marked 0).space) ∩ Z
  let C := ((N.space ∩ (T.marked 1).space) ∩ Z) ∪ (N.space ∩ (T.marked 2).space)
  obtain ⟨hhalf, _, hout⟩ := T.vertex_half_ball_pairs p w hw
  have hrim : O ∪ C = (T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ Z) ∪
      T.diskDualBase {(p : T.index → ℝ × V3)} := by
    have hq : T.dualRegionRim {(p : T.index → ℝ × V3)} =
        ((N.link p).space ∩ (T.marked 0).space) ∪ (N.space ∩ (T.marked 1).space) := by
      dsimp only [dualRegionRim]
      rw [Finset.centroid_singleton]
      rfl
    rw [hq, T.vertex_base_eq_inter]
    ext x
    change (x ∈ O ∨ x ∈ C) ↔ _
    simp only [O, C, mem_union, mem_inter_iff]
    tauto
  have hball : IsFinitePLBallPair C3 (T.dualRegion {(p : T.index → ℝ × V3)} ∩ Z)
      ((T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ Z) ∪
        T.diskDualBase {(p : T.index → ℝ × V3)}) := by
    change IsFinitePLBallPair C3 (T.dualRegion {(p : T.index → ℝ × V3)} ∩ Z)
      (O ∪ C) at hhalf
    rwa [hrim] at hhalf
  refine ⟨hball, ?_⟩
  obtain ⟨x, hx, hnot⟩ := hout
  refine ⟨x, hrim.subset (Or.inl hx), ?_⟩
  intro hxB
  exact hnot (Or.inr ((T.vertex_base_eq_inter p).subset hxB))

end PoincareConjecture.M76.OriginalProperDiskTriangulation
