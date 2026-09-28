import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubpolyhedronZeroSet
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_finitePL_square_rim_height :
    ∃ h : V2 → ℝ, FinitePiecewiseAffineOn h D ∧
      ∀ x ∈ D, h x ∈ Icc (0 : ℝ) (1 / 2) ∧ (h x = 0 ↔ x ∈ Q) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨J, hJ, hJQ⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨h, hPL, hh⟩ := K.exists_finitePL_subpolyhedron_zero_set J hK hJ
    (hJQ.subset.trans (sphere_subset_closedBall.trans hKD.symm.subset))
    (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨h, hKD ▸ hPL, ?_⟩
  intro x hx
  have hbound := hh x (hKD.symm.subset hx)
  simpa only [hJQ] using hbound

end PoincareConjecture.M76.Dehn
