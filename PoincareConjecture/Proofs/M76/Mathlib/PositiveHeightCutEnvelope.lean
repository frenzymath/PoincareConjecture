import PoincareConjecture.Proofs.M76.Mathlib.ConvexCylinderRadialGeometry
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsCompact.exists_positive_height_cut_frontier
    {Q : Set E} (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : Q = {x | ∀ i, L i x ≤ 1})
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) {β : ℝ} (hβ : 0 < β) :
    ∃ (M : (ι ⊕ Unit) → E →ₗ[ℝ] ℝ) (K : SimplicialComplex ℝ E),
      (∀ i, M i ≠ 0) ∧
      Q ∩ {x | A x ≤ β} = {x | ∀ i, M i x ≤ 1} ∧
      IsCompact (Q ∩ {x | A x ≤ β}) ∧ Convex ℝ (Q ∩ {x | A x ≤ β}) ∧
      (0 : E) ∈ interior (Q ∩ {x | A x ≤ β}) ∧
      K.faces.Finite ∧ K.space = frontier (Q ∩ {x | A x ≤ β}) ∧
      Q ∩ {x | A x = β} ⊆ frontier (Q ∩ {x | A x ≤ β}) ∧
      ∃ p ∈ frontier (Q ∩ {x | A x ≤ β}), A p < 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let M : (ι ⊕ Unit) → E →ₗ[ℝ] ℝ := Sum.elim L (fun _ => β⁻¹ • A)
  have hM (i : ι ⊕ Unit) : M i ≠ 0 := by
    cases i with
    | inl i => exact hL i
    | inr u => exact smul_ne_zero (inv_ne_zero hβ.ne') hA
  let R := Q ∩ {x | A x ≤ β}
  have hRrep : R = {x | ∀ i, M i x ≤ 1} := by
    ext x
    constructor
    · intro hx i
      cases i with
      | inl i => exact (hrep.subset hx.1) i
      | inr u =>
        change β⁻¹ * A x ≤ 1
        rw [← div_eq_inv_mul, div_le_one hβ]
        exact hx.2
    · intro hx
      refine ⟨hrep.symm.subset (fun i => hx (Sum.inl i)), ?_⟩
      have h := hx (Sum.inr ())
      change β⁻¹ * A x ≤ 1 at h
      rwa [← div_eq_inv_mul, div_le_one hβ] at h
  have hRc : IsCompact R :=
    hQ.inter_right (isClosed_le A.continuous_of_finiteDimensional continuous_const)
  have hRcv : Convex ℝ R := hcv.inter ((convex_Iic β).linear_preimage A)
  have hR0 : (0 : E) ∈ interior R := by
    rw [hRrep, interior_finite_linear_unit_halfspaces M hM]
    intro i
    simp only [map_zero, zero_lt_one]
  let B : (ι ⊕ Unit) → E →ᵃ[ℝ] ℝ := fun i =>
    (M i).toAffineMap - AffineMap.const ℝ E 1
  let H := Finset.univ.image B
  have hRaff : R = {x | ∀ b ∈ H, b x ≤ 0} := by
    rw [hRrep]
    ext x
    simp only [H, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, B, AffineMap.coe_sub, Pi.sub_apply,
      LinearMap.coe_toAffineMap, AffineMap.const_apply, sub_nonpos]
  obtain ⟨J, hJ, hJR⟩ := hRc.exists_finite_triangulation_of_halfspaces H hRaff
  have htop : Q ∩ {x | A x = β} ⊆ frontier R := by
    intro x hx
    rw [hRrep, frontier_finite_linear_unit_halfspaces M hM]
    refine ⟨hRrep.subset ⟨hx.1, hx.2.le⟩, Sum.inr (), ?_⟩
    change β⁻¹ * A x = 1
    rw [hx.2, inv_mul_cancel₀ hβ.ne']
  obtain ⟨v, hv⟩ := LinearMap.surjective hA (-1 : ℝ)
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hv
    norm_num at hv
  obtain ⟨hr, hp⟩ := hRc.gauge_inv_smul_mem_frontier hRcv hR0 hvne
  have hnegative : A ((gauge R v)⁻¹ • v) < 0 := by
    rw [map_smul, smul_eq_mul, hv, mul_neg_one]
    exact neg_neg_of_pos hr
  exact ⟨M, J.frontierSubcomplex R, hM, hRrep, hRc, hRcv, hR0,
    J.frontierSubcomplex_finite R hJ,
    J.frontierSubcomplex_space hRc.isClosed hRcv ⟨0, hR0⟩ hJR,
    htop, _, hp, hnegative⟩

end Set
