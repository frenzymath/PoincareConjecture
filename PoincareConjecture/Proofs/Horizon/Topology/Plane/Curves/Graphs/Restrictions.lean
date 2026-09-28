import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.TransverseCuts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff

namespace Poincare.Topology.Plane.Curves.TransverseGraphCuts

variable {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
  (P : TransverseGraphCuts lo a b ua wa ub wb)
  {r : ℝ} (hr : 0 < r) (hrP : r ≤ P.radius)

def restrictRadius : TransverseGraphCuts lo a b ua wa ub wb where
  left := P.left
  right := P.right
  radius := r
  radius_pos := hr
  height_subset := fun _ hz => P.height_subset
    ⟨by linarith [hz.1], hz.2.trans_le hrP⟩
  separated := fun _ hz => P.separated _
    ⟨by linarith [hz.1], hz.2.trans_le hrP⟩

@[simp] theorem restrictRadius_left : (P.restrictRadius hr hrP).left = P.left := rfl

@[simp] theorem restrictRadius_right : (P.restrictRadius hr hrP).right = P.right := rfl

@[simp] theorem restrictRadius_radius : (P.restrictRadius hr hrP).radius = r := rfl

theorem restrictRadius_coordinates_apply
    {X Y : Set ℝ} (hX : IsOpen X) (hloX : ContDiffOn ℝ ∞ lo X)
    (hY : IsOpen Y) (hloY : ContDiffOn ℝ ∞ lo Y) (q : ℝ × ℝ) :
    (P.restrictRadius hr hrP).coordinates hX hloX q = P.coordinates hY hloY q := by
  rw [coordinates_apply, coordinates_apply]
  rfl

theorem restrictRadius_coordinates_source_subset
    {X Y : Set ℝ} (hX : IsOpen X) (hloX : ContDiffOn ℝ ∞ lo X)
    (hY : IsOpen Y) (hloY : ContDiffOn ℝ ∞ lo Y) (hXY : X ⊆ Y) :
    ((P.restrictRadius hr hrP).coordinates hX hloX).source ⊆
      (P.coordinates hY hloY).source := by
  intro q hq
  rw [coordinates, obliqueStripCoordinates_source] at hq ⊢
  exact ⟨⟨(neg_le_neg hrP).trans_lt hq.1.1, hq.1.2.trans_le hrP⟩, hXY hq.2⟩

end Poincare.Topology.Plane.Curves.TransverseGraphCuts
