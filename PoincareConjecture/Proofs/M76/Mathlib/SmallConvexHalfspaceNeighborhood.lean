import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry

set_option autoImplicit false

open Set Metric Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]

theorem IsOpen.exists_small_convex_halfspace_frontier
    {U : Set E} (hU : IsOpen U) (hzero : (0 : E) ∈ U)
    (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ (C : Set E) (L : (ι ⊕ ι) → E →ₗ[ℝ] ℝ)
      (K : SimplicialComplex ℝ E),
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧ C ⊆ U ∧
      (∀ i, L i ≠ 0) ∧ C = {x | ∀ i, L i x ≤ 1} ∧
      K.faces.Finite ∧ K.space = frontier C := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hV : IsOpen (c '' U) := c.toHomeomorph.isOpenMap U hU
  have h0V : (0 : ι → ℝ) ∈ c '' U := ⟨0, hzero, map_zero c⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  let C : Set E := c ⁻¹' closedBall (0 : ι → ℝ) r
  have hC : IsCompact C := c.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hcv : Convex ℝ C := (convex_closedBall (0 : ι → ℝ) r).linear_preimage c.toLinearMap
  have h0C : (0 : E) ∈ interior C := by
    change (0 : E) ∈ interior (c.toHomeomorph ⁻¹' closedBall (0 : ι → ℝ) r)
    rw [← c.toHomeomorph.preimage_interior]
    change c 0 ∈ interior (closedBall (0 : ι → ℝ) r)
    simpa only [map_zero] using
      (ball_subset_interior_closedBall (Metric.mem_ball_self (x := (0 : ι → ℝ)) hr))
  have hCU : C ⊆ U := by
    intro x hx
    have hnorm : ‖c x‖ ≤ r := by
      change c x ∈ closedBall (0 : ι → ℝ) r at hx
      simpa only [mem_closedBall, dist_zero_right] using hx
    have hnear : c x ∈ ball (0 : ι → ℝ) ε := by
      rw [mem_ball, dist_zero_right]
      exact hnorm.trans_lt (half_lt_self hε)
    obtain ⟨y, hy, hyx⟩ := hball hnear
    exact (c.injective hyx) ▸ hy
  let L : (ι ⊕ ι) → E →ₗ[ℝ] ℝ := fun i =>
    r⁻¹ • (signedCubeCoordinate i).comp c.toLinearMap
  have hL (i : ι ⊕ ι) : L i ≠ 0 := by
    intro he
    apply signedCubeCoordinate_ne_zero i
    apply LinearMap.ext
    intro y
    have h := congrArg (fun f : E →ₗ[ℝ] ℝ => f (c.symm y)) he
    change r⁻¹ * signedCubeCoordinate i (c (c.symm y)) = 0 at h
    rw [c.apply_symm_apply] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hr.ne')
  have hrep : C = {x | ∀ i, L i x ≤ 1} := by
    ext x
    change ‖c x - 0‖ ≤ r ↔ ∀ i, L i x ≤ 1
    rw [sub_zero]
    have hform (i : ι ⊕ ι) : L i x ≤ 1 ↔ signedCubeCoordinate i (c x) ≤ r := by
      change r⁻¹ * signedCubeCoordinate i (c x) ≤ 1 ↔ _
      rw [← div_eq_inv_mul, div_le_one hr]
    simp_rw [hform]
    constructor
    · exact fun hx i => (signedCubeCoordinate_le_norm i (c x)).trans hx
    · intro hx
      apply (pi_norm_le_iff_of_nonneg hr.le).mpr
      intro i
      rw [Real.norm_eq_abs]
      have hp : c x i ≤ r := hx (.inl i)
      have hn : -c x i ≤ r := hx (.inr i)
      exact abs_le.mpr ⟨by linarith, hp⟩
  let A : (ι ⊕ ι) → E →ᵃ[ℝ] ℝ := fun i =>
    (L i).toAffineMap - AffineMap.const ℝ E 1
  let H := Finset.univ.image A
  have hrepA : C = {x | ∀ a ∈ H, a x ≤ 0} := by
    rw [hrep]
    ext x
    simp only [H, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, A, AffineMap.coe_sub, Pi.sub_apply,
      LinearMap.coe_toAffineMap, AffineMap.const_apply, sub_nonpos]
  obtain ⟨J, hJ, hJC⟩ := hC.exists_finite_triangulation_of_halfspaces H hrepA
  exact ⟨C, L, J.frontierSubcomplex C, hC, hcv, h0C, hCU, hL, hrep,
    J.frontierSubcomplex_finite C hJ,
    J.frontierSubcomplex_space hC.isClosed hcv ⟨0, h0C⟩ hJC⟩

end Set
