import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Deletion.Ambient
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Triangle.Normalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.VertexMotion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Cyclic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.Admissible

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private instance : Fact (Module.finrank ℝ E2 = 2) := ⟨by simp⟩

theorem exists_uniform_ambient_diffeomorph_rounded_polygon
    (e : ℂ ≃ₗᵢ[ℝ] E2) (o : Orientation ℝ E2 (Fin 2))
    {n : ℕ} (p : Polygon E2 (n + 3)) (hp : IsSimplePolygon p) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ < d → ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
        (∀ s, δ ≤ |s| → ρ s = |s|) →
        (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) → (∀ s, |deriv ρ s| ≤ 1) →
        ∃ F : E2 ≃ₘ[ℝ] E2,
          F '' sphere (0 : E2) 1 = range (roundedPolygonParameter ρ p) := by
  induction n with
  | zero =>
    refine ⟨2 / 9, by norm_num, by norm_num, ?_⟩
    intro δ hδ hδsmall ρ hρ htail hbound hder
    exact exists_ambient_diffeomorph_rounded_triangle e hp hδ hδsmall htail hbound hρ hder
  | succ n ih =>
    obtain ⟨k, _, _, had, _⟩ := hp.exists_admissible_vertex_away_edge (by simp) (by omega) 0
    let q := polygonPushVertex p k 1
    have hq : IsSimplePolygon q := hp.isSimple_polygonPushVertex k had (by simp)
    let r := polygonCyclicShift q (finRotate (n + 4) k)
    have hr : IsSimplePolygon r := hq.cyclicShift _
    have hmid : r (Fin.last (n + 3)) = midpoint ℝ (r (Fin.last (n + 2)).castSucc) (r 0) :=
      polygonCyclicShift_last_midpoint q k (hp.polygonPushVertex_one_midpoint k)
    have hstraight : r (Fin.last (n + 3)) ∈
        segment ℝ (r ((finRotate (n + 4)).symm (Fin.last (n + 3))))
          (r (finRotate (n + 4) (Fin.last (n + 3)))) := by
      have hprev : (finRotate (n + 4)).symm (Fin.last (n + 3)) =
          (Fin.last (n + 2)).castSucc := by
        apply (finRotate (n + 4)).injective
        rw [Equiv.apply_symm_apply]
        exact (finRotate_of_lt (Fin.last (n + 2)).isLt).symm
      rw [hprev, finRotate_last, hmid]
      exact midpoint_mem_segment _ _
    let s := polygonDeleteVertex r (Fin.last (n + 3))
    have hs : IsSimplePolygon s := hr.isSimple_polygonDeleteVertex _ hstraight
    obtain ⟨d₀, hd₀, hd₀small, hpush⟩ := exists_uniform_ambient_rounded_vertex_push e o hp k had
    obtain ⟨d₁, hd₁, hd₁small, hdelete⟩ := exists_uniform_ambient_delete_last_midpoint e o hr hmid
    obtain ⟨d₂, hd₂, hd₂small, hnormalize⟩ := ih s hs
    refine ⟨min d₀ (min d₁ d₂), lt_min hd₀ (lt_min hd₁ hd₂),
      (min_le_left _ _).trans_lt (by linarith), ?_⟩
    intro δ hδ hδsmall ρ hρ htail hbound hder
    have hδ₀ : δ < d₀ := hδsmall.trans_le (min_le_left _ _)
    have hδ₁ : δ < d₁ := hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hδ₂ : δ < d₂ := hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨A, _, hA⟩ := hpush δ hδ hδ₀ ρ hρ htail hbound hder
    obtain ⟨B, _, hB⟩ := hdelete δ hδ hδ₁ ρ hρ htail hbound hder
    obtain ⟨C, hC⟩ := hnormalize δ hδ hδ₂ ρ hρ htail hbound hder
    have hshift : range (roundedPolygonParameter ρ r) = range (roundedPolygonParameter ρ q) :=
      range_roundedPolygonParameter_cyclicShift ρ q _
    have hBA : (A.trans B) '' range (roundedPolygonParameter ρ p) =
        range (roundedPolygonParameter ρ s) := by
      change (fun x => B (A x)) '' _ = _
      rw [← image_image B A, hA, ← hshift]
      exact hB
    refine ⟨C.trans (A.trans B).symm, ?_⟩
    change (fun x => (A.trans B).symm (C x)) '' _ = _
    rw [← image_image (A.trans B).symm C, hC, ← hBA]
    exact (A.trans B).toEquiv.symm_image_image _

end Poincare.Manifold.Schoenflies.Plane
