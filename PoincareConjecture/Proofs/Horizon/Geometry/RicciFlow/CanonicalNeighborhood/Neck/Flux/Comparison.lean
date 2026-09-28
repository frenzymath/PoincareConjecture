import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith











set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NeckFlux

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]



theorem scalar_le_of_flux_comparison
    {R₁ R₂ α₁ α₂ C : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hα₁ : 0 < α₁) (hα : α₂ ≤ C * α₁)
    (hflux : 0 ≤ α₂ / R₂ - α₁ / R₁) :
    R₂ ≤ C * R₁ := by
  have hprod : α₁ * R₂ ≤ α₂ * R₁ :=
    (div_le_div_iff₀ hR₁ hR₂).mp (le_of_sub_nonneg hflux)
  apply le_of_mul_le_mul_left (a := α₁) _ hα₁
  calc
    α₁ * R₂ ≤ α₂ * R₁ := hprod
    _ ≤ (C * α₁) * R₁ := mul_le_mul_of_nonneg_right hα hR₁.le
    _ = α₁ * (C * R₁) := by ring



theorem scalar_le_twice_of_flux_error
    {R₁ R₂ α₁ α₂ δ : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hδ : δ ≤ 1 / 3)
    (hinner : |α₁ - 1| ≤ δ) (houter : |α₂ - 1| ≤ δ)
    (hflux : 0 ≤ α₂ / R₂ - α₁ / R₁) :
    R₂ ≤ 2 * R₁ := by
  have hi := (abs_le.mp hinner).1
  have ho := (abs_le.mp houter).2
  exact scalar_le_of_flux_comparison hR₁ hR₂ (by linarith) (by linarith) hflux



theorem scale_ge_of_scalar_center_le
    {g : RiemannianMetric 3 M} (N₁ N₂ : EpsilonNeck g) {C : ℝ}
    (hC : 0 < C)
    (hscalar : N₂.connection.scalarCurvature N₂.center ≤
      C * N₁.connection.scalarCurvature N₁.center) :
    C ^ (-1 / 2 : ℝ) * N₁.scale ≤ N₂.scale := by
  rw [N₁.scale_eq_scalar, N₂.scale_eq_scalar]
  have h₁ : 0 < N₁.connection.scalarCurvature N₁.center := N₁.scalar_center_pos
  have h₂ : 0 < N₂.connection.scalarCurvature N₂.center := N₂.scalar_center_pos
  have hpow := Real.rpow_le_rpow_of_nonpos h₂ hscalar (by norm_num :
    (-1 / 2 : ℝ) ≤ 0)
  calc
    C ^ (-1 / 2 : ℝ) *
        N₁.connection.scalarCurvature N₁.center ^ (-1 / 2 : ℝ) =
      (C * N₁.connection.scalarCurvature N₁.center) ^ (-1 / 2 : ℝ) :=
        (Real.mul_rpow (le_of_lt hC) h₁.le).symm
    _ ≤ N₂.connection.scalarCurvature N₂.center ^ (-1 / 2 : ℝ) := hpow

end PoincareConjecture.NeckFlux
