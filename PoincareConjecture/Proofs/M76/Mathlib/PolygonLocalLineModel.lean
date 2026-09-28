import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalEdges
import PoincareConjecture.Proofs.M76.Mathlib.PlanarCornerLocalModel
import PoincareConjecture.Proofs.M76.Mathlib.LocalPlanarSides

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Polygon

variable {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
  (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)

include hP hinj

theorem exists_local_line_model {q : ℝ × ℝ} (hq : q ∈ P.boundary ℝ) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (e q).2 = 0 ∧
      ∀ᶠ x in 𝓝 q, x ∈ P.boundary ℝ ↔ (e x).2 = 0 := by
  by_cases hqv : q ∈ range P
  · obtain ⟨i, rfl⟩ := hqv
    have hn (j : Fin (n + 3)) : finRotate (n + 3) j ≠ j := by
      rw [finRotate_apply]
      intro h
      have h1 : (1 : Fin (n + 3)) = 0 := add_left_cancel
        (show j + 1 = j + 0 by simpa only [add_zero] using h)
      have hval := congrArg Fin.val h1
      change 1 % (n + 3) = 0 at hval
      rw [Nat.mod_eq_of_lt (by omega)] at hval
      exact Nat.one_ne_zero hval
    have hp : (finRotate (n + 3)).symm i ≠ i := by
      intro h
      exact hn i (by simpa only [Equiv.apply_symm_apply] using
        (congrArg (finRotate (n + 3)) h).symm)
    have hinter : segment ℝ (P ((finRotate (n + 3)).symm i)) (P i) ∩
        segment ℝ (P i) (P (finRotate (n + 3) i)) ⊆ {P i} := by
      simpa only [edgeSet, Equiv.apply_symm_apply, affineSegment_eq_segment] using
        (P.adjacent_edgeSet_inter hP hinj ((finRotate (n + 3)).symm i)).subset
    obtain ⟨e, he, hlocal⟩ := exists_local_line_of_segment_corner
      (hinj.ne hp) (hinj.ne (hn i)) hinter
    refine ⟨e, he, ?_⟩
    filter_upwards [P.eventually_boundary_iff_adjacent_edges hP hinj i, hlocal] with x hx hy
    exact hx.trans (by simpa only [edgeSet, Equiv.apply_symm_apply,
      affineSegment_eq_segment] using hy)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    obtain ⟨e, he, hlocal⟩ := PlanarSegment.exists_local_line
      (show q ∈ segment ℝ (P i) (P (finRotate (n + 3) i)) by
        simpa only [edgeSet, affineSegment_eq_segment] using hi)
      (fun h => hqv ⟨i, h.symm⟩) (fun h => hqv ⟨_, h.symm⟩)
    refine ⟨e, he, ?_⟩
    filter_upwards [P.eventually_boundary_iff_single_edge hP hinj hqv hi, hlocal] with x hx hy
    exact hx.trans (by simpa only [edgeSet, affineSegment_eq_segment] using hy)

theorem hasLocalComplementarySides_boundary :
    (P.boundary ℝ).HasLocalComplementarySides :=
  Set.hasLocalComplementarySides_of_local_line_models
    (fun _ hq => P.exists_local_line_model hP hinj hq)

end Polygon
