import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryRadial
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry










set_option autoImplicit false

open Set NormedSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem IsCompact.gauge_inv_smul_mem_frontier {s : Set E} (hs : IsCompact s)
    (hcv : Convex ℝ s) (hzero : (0 : E) ∈ interior s) {x : E} (hx : x ≠ 0) :
    0 < (gauge s x)⁻¹ ∧ (gauge s x)⁻¹ • x ∈ frontier s := by
  have hnhds : s ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hzero
  have hpos : 0 < gauge s x := (gauge_pos (absorbent_nhds_zero hnhds)
    (isVonNBounded_of_isBounded ℝ hs.isBounded)).mpr hx
  refine ⟨inv_pos.mpr hpos, (gauge_eq_one_iff_mem_frontier hcv hnhds).mp ?_⟩
  rw [gauge_smul_of_nonneg (inv_nonneg.mpr hpos.le), smul_eq_mul,
    inv_mul_cancel₀ hpos.ne']




theorem IsCompact.exists_frontier_normalize_eq {s : Set E} (hs : IsCompact s)
    (hcv : Convex ℝ s) (hzero : (0 : E) ∈ interior s) {x : E} (hx : x ≠ 0) :
    ∃ y ∈ frontier s, normalize y = normalize x := by
  obtain ⟨hpos, hmem⟩ := hs.gauge_inv_smul_mem_frontier hcv hzero hx
  exact ⟨_, hmem, normalize_smul_of_pos hpos x⟩

variable [FiniteDimensional ℝ E]





theorem frontier_finite_linear_unit_halfspaces {ι : Type*} [Finite ι]
    (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0) :
    frontier {x | ∀ i, L i x ≤ 1} =
      {x | (∀ i, L i x ≤ 1) ∧ ∃ i, L i x = 1} := by
  let A : ι → E →ᵃ[ℝ] ℝ := fun i => (L i).toAffineMap - AffineMap.const ℝ E 1
  have hA : ∀ i, (A i).linear ≠ 0 := by
    intro i
    simpa [A] using hL i
  have h := frontier_finite_affine_halfspaces A hA
  simpa only [A, AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
    AffineMap.const_apply, sub_nonpos, sub_eq_zero] using h




theorem linear_maximum_eq_one_of_radial_frontier {ι : Type*} [Finite ι]
    (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    {x : E} {r : ℝ} (hr : 0 < r) {i : ι} (hi : ∀ j, L j x ≤ L i x)
    (hfront : r • x ∈ frontier {y | ∀ j, L j y ≤ 1}) : L i (r • x) = 1 := by
  rw [frontier_finite_linear_unit_halfspaces L hL] at hfront
  obtain ⟨hle, j, hj⟩ := hfront
  apply le_antisymm (hle i)
  rw [← hj]
  simpa only [map_smul, smul_eq_mul] using mul_le_mul_of_nonneg_left (hi j) hr.le
