import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.Mathlib.CubePrismBoundary

/-!
# The actual cube-sphere chart of a whole prism frontier

Normalize the entire finite PL ball pair, then restrict its inverse
to the complete specified boundary. See rigidity042, section4.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "D3" => closedBall (0 : V3) 1
local notation "Q3" => sphere (0 : V3) 1

/-- Construct a finite PL homeomorphism from the entire literal
V3 cube sphere to the complete prism boundary. See042, section4. -/
theorem exists_finitePL_cubePrismBoundary_sphere {a b : ℝ} (hab : a < b) :
    ∃ h : Q3 ≃ₜ cubePrismBoundary a b, h.IsFinitePL := by
  let c : E ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  have hball := isFinitePLBallPair_cubePrism hab
  obtain ⟨H, hH, hboundary⟩ := hball.exists_cube_chart c
  have hinverse (x : D3) : (x : V3) ∈ Q3 ↔
      (H.symm x : E) ∈ cubePrismBoundary a b := by
    have h := hboundary (H.symm x)
    rw [H.apply_symm_apply, frontier_closedBall _ one_ne_zero] at h
    exact h.symm
  obtain ⟨J, hJ, hJQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  exact ⟨H.symm.restrictSubsets sphere_subset_closedBall hball.1 hinverse,
    hH.symm.restrictSubsets sphere_subset_closedBall hball.1 hinverse J hJ hJQ⟩

end PoincareMT.M76
