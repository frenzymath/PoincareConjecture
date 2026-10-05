import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.StandardHierarchyCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Isotopy.Mathlib.HomotopyFundamentalGroup
import Mathlib.Analysis.Convex.MetricSpace

/-!
# Fundamental groups of the literal interval-circle annulus

Contract the closed interval factor along affine segments while retaining the
circle coordinate. The actual projection and every constant-interval section
therefore induce bijections on the original based fundamental groups.
-/

set_option autoImplicit false
open Set Metric

namespace PoincareMT.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "D" => closedBall (0 : V1) 1
local notation "C" => AddCircle (4 * (128 : ℝ))

/-- The interval-circle projection and the section at the supplied interval
point are inverse up to the actual affine interval contraction. -/
noncomputable def annulusProjectionHomotopyEquiv (b : D) :
    ContinuousMap.HomotopyEquiv (D × C) C := by
  let q : C(D × C, C) := ⟨Prod.snd, continuous_snd⟩
  let s : C(C, D × C) := ⟨fun z => (b, z), continuous_const.prodMk continuous_id⟩
  let G : (s.comp q).Homotopy (ContinuousMap.id (D × C)) :=
    { toFun := fun z =>
        (⟨(1 - (z.1 : ℝ)) • (b : V1) + (z.1 : ℝ) • (z.2.1 : V1),
          (convex_closedBall (0 : V1) 1) b.property z.2.1.property
            (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 _)⟩,
          z.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro x
        apply Prod.ext
        · apply Subtype.ext
          simp [s, q]
        · rfl
      map_one_left := by
        intro x
        apply Prod.ext
        · apply Subtype.ext
          simp
        · rfl }
  exact
    { toFun := q
      invFun := s
      left_inv := ⟨G⟩
      right_inv := by
        have h : q.comp s = ContinuousMap.id C := by ext x; rfl
        rw [h] }

/-- Projection to the circle induces a bijection at every annulus basepoint. -/
theorem annulus_projection_pi1_bijective (x : D × C) :
    Function.Bijective (FundamentalGroup.map
      (⟨Prod.snd, continuous_snd⟩ : C(D × C, C)) x) :=
  FundamentalGroup.map_bijective_of_homotopyEquiv
    (annulusProjectionHomotopyEquiv x.1) x

/-- Every literal constant-interval section induces a bijection at each of
its circle basepoints, including either boundary circle. -/
theorem annulus_section_pi1_bijective (b : D) (c : C) :
    Function.Bijective (FundamentalGroup.map
      (⟨fun z : C => (b, z), continuous_const.prodMk continuous_id⟩ : C(C, D × C)) c) :=
  FundamentalGroup.map_bijective_of_homotopyEquiv
    (annulusProjectionHomotopyEquiv b).symm c

end PoincareMT.M76.HamiltonIntervalTorus
