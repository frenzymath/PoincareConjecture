import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Vertices.HalfBlocks

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

open Classical in

theorem vertex_half_ballPair_and_outside (p : (T.marked 2).vertices)
    (w : ℝ) (hw : w ≠ 0) :
    let Z : Set E :=
      {x | 0 ≤ w * (T.chart p x).2}
    IsFinitePLBallPair C3 (T.dualRegion {(p : E)} ∩ Z)
      ((T.dualRegionRim {(p : E)} ∩ Z) ∪
        T.surfaceBase {(p : E)}) ∧
      (((T.dualRegionRim {(p : E)} ∩ Z) ∪
          T.surfaceBase {(p : E)}) \
        T.surfaceBase {(p : E)}).Nonempty := by
  classical
  let N := T.vertexBlock p
  let Z : Set E :=
    {x | 0 ≤ w * (T.chart p x).2}
  let O := ((N.link p).space ∩ (T.marked 0).space) ∩ Z
  let C := ((N.space ∩ (T.marked 1).space) ∩ Z) ∪ (N.space ∩ (T.marked 2).space)
  obtain ⟨hhalf, _, hout⟩ := T.vertex_half_ball_pairs p w hw
  have hrim : O ∪ C = (T.dualRegionRim {(p : E)} ∩ Z) ∪
      T.surfaceBase {(p : E)} := by
    have hq : T.dualRegionRim {(p : E)} =
        ((N.link p).space ∩ (T.marked 0).space) ∪ (N.space ∩ (T.marked 1).space) := by
      dsimp only [dualRegionRim]
      rw [Finset.centroid_singleton]
      rfl
    rw [hq, T.vertex_base_eq_inter]
    ext x
    change (x ∈ O ∨ x ∈ C) ↔ _
    simp only [O, C, mem_union, mem_inter_iff]
    tauto
  have hball : IsFinitePLBallPair C3 (T.dualRegion {(p : E)} ∩ Z)
      ((T.dualRegionRim {(p : E)} ∩ Z) ∪
        T.surfaceBase {(p : E)}) := by
    change IsFinitePLBallPair C3 (T.dualRegion {(p : E)} ∩ Z)
      (O ∪ C) at hhalf
    rwa [hrim] at hhalf
  refine ⟨hball, ?_⟩
  obtain ⟨x, hx, hnot⟩ := hout
  refine ⟨x, hrim.subset (Or.inl hx), ?_⟩
  intro hxB
  exact hnot (Or.inr ((T.vertex_base_eq_inter p).subset hxB))

end Geometry.SimplicialComplex.CoorientedSurfaceStars
