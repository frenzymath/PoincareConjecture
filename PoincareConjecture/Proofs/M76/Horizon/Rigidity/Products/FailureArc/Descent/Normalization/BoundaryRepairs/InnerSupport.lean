import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Endpoint
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchInnerSupport
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchMotionSupport



set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}
  {step : Step s t} {j : P2 → t.Carrier} {R Fmark : Set M}
  {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
  (A : PlanarAnnulusBoundaryMotion step j R Fmark a b W ε)

theorem exists_inner_change_support :
    ∃ Small : Set t.Carrier, IsCompact Small ∧
      IsCompact (Small ∪ A.ambient 1 '' Small) ∧
      Small ∪ A.ambient 1 '' Small ⊆
        (A.window.right.trans A.chart).symm '' interior A.support.space ∧
      Small ⊆ (step.projection ∘ step.inclusion) ⁻¹' W ∧
      (∀ u, EqOn (A.ambient u) id (j '' Ann \ Small)) ∧
      (∀ u, EqOn (A.ambient u) id ((step.projection ∘ step.inclusion) ⁻¹' W)ᶜ) ∧
      step.projection (step.inclusion (j a)) ∈ (step.projection ∘ step.inclusion) '' Small := by
  let T := A.window.right.trans A.chart
  let Small := T.symm '' closedBall (0 : V3) A.radius
  obtain ⟨hS, hSend, hSinner, hfix⟩ := branch_disk_change_support_with_endpoint T
    (j '' Ann) A.support.space A.source.space A.fixed.space A.radius
    A.closed_clearance A.support_right_target A.source_space A.fixed_space
    A.motion A.ambient A.formula A.outside A.protected_fixed
  have hSW : Small ⊆ (step.projection ∘ step.inclusion) ⁻¹' W := by
    apply (image_mono (A.closed_clearance.trans interior_subset)).trans
    exact right_branch_chart_support_subset A.window A.chart A.support_target
      (fun _ hz => (A.chart_inside hz).2) (fun _ hz => (A.chart_inside hz).1)
  refine ⟨Small, hS, hSend, hSinner, hSW, hfix, ?_, ?_⟩
  · intro u
    exact right_branch_motion_fixed_off_window A.window A.chart A.support_target
      (fun _ hz => (A.chart_inside hz).2) (fun _ hz => (A.chart_inside hz).1) (A.outside u)
  · have hzeroBall : (0 : V3) ∈ closedBall (0 : V3) A.radius :=
      mem_closedBall_self A.radius_pos.le
    have hzeroT := A.support_right_target (interior_subset (A.closed_clearance hzeroBall))
    refine ⟨T.symm 0, ⟨0, hzeroBall, rfl⟩, ?_⟩
    have hzeroQ : (0 : V3) ∈ A.chart.target := A.centered ▸ A.chart.map_source A.point
    change (step.projection ∘ step.inclusion) (A.window.right.symm (A.chart.symm 0)) = _
    rw [← congrFun A.window.right_eq _, A.window.right.right_inv hzeroT.2,
      ← A.centered, A.chart.left_inv A.point]

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
