import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalFrontier











set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem interior_finite_linear_unit_halfspaces [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι]
    (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0) :
    interior {x | ∀ i, L i x ≤ 1} = {x | ∀ i, L i x < 1} := by
  let A : ι → E →ᵃ[ℝ] ℝ := fun i => (L i).toAffineMap - AffineMap.const ℝ E 1
  have hA : ∀ i, (A i).linear ≠ 0 := by
    intro i
    simpa [A] using hL i
  simpa only [A, AffineMap.coe_sub, Pi.sub_apply, LinearMap.coe_toAffineMap,
    AffineMap.const_apply, sub_nonpos, sub_neg] using
      interior_finite_affine_halfspaces A hA




theorem exists_unit_le_of_not_mem_interior [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι]
    (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0) {Q : Set E}
    (hQ : Q = {x | ∀ i, L i x ≤ 1}) {x : E} (hx : x ∉ interior Q) :
    ∃ i, 1 ≤ L i x := by
  rw [hQ, interior_finite_linear_unit_halfspaces L hL] at hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact ⟨i, not_lt.mp hi⟩




theorem Convex.one_le_of_smul_top_mem_frontier_cylinder {Q : Set E}
    (hcv : Convex ℝ Q) (h0 : (0 : E) ∈ interior Q) {x : E} (hx : x ∈ Q)
    {r : ℝ} (hr : 0 < r)
    (hf : r • (x, (1 : ℝ)) ∈ frontier (Q ×ˢ Icc (-1 : ℝ) 2)) : 1 ≤ r := by
  by_contra h
  have hr1 : r < 1 := lt_of_not_ge h
  have hri : r • x ∈ interior Q := by
    simpa only [smul_zero, zero_add] using hcv.combo_interior_self_mem_interior
      h0 hx (sub_pos.mpr hr1) hr.le (sub_add_cancel (1 : ℝ) r)
  apply hf.2
  rw [interior_prod_eq, interior_Icc]
  refine ⟨hri, ?_, ?_⟩
  · change -1 < r * 1
    linarith
  · change r * 1 < 2
    linarith




theorem LinearMap.mul_height_le_one_of_unit_le (L : E →ₗ[ℝ] ℝ)
    {x : E} {r t : ℝ} (hr : 0 ≤ r) (ht : t ≤ 1)
    (hx : 1 ≤ L x) (himage : L (r • x) ≤ 1) : r * t ≤ 1 := by
  have hr1 : r ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hx hr
    rw [map_smul, smul_eq_mul] at himage
    nlinarith
  calc
    r * t ≤ r * 1 := mul_le_mul_of_nonneg_left ht hr
    _ = r := mul_one r
    _ ≤ 1 := hr1





theorem Set.bottom_or_not_mem_inner_of_mem_cylinderExterior {Q C : Set E}
    (hQC : Q ⊆ interior C) {q : E × ℝ}
    (hq : q ∈ frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior Q ×ˢ {1}) :
    q.2 = -1 ∨ q.1 ∉ interior Q := by
  have hfront : q ∈ (closure C ×ˢ {(-1 : ℝ), 1}) ∪
      (frontier C ×ˢ closure (Icc (-1 : ℝ) 1)) := by
    simpa only [frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)] using
      (frontier_prod_eq C (Icc (-1 : ℝ) 1)).subset hq.1
  rcases hfront with htop | hside
  · have ht : q.2 = -1 ∨ q.2 = 1 := by
      simpa only [mem_insert_iff, mem_singleton_iff] using htop.2
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr (fun hx => hq.2 ⟨hx, ht⟩)
  · exact Or.inr (fun hx => hside.1.2 (hQC (interior_subset hx)))

namespace LinearMap




noncomputable def cylinderUnitForms {ι : Type*} (L : ι → E →ₗ[ℝ] ℝ) :
    ι ⊕ Bool → (E × ℝ) →ₗ[ℝ] ℝ
  | Sum.inl i => (L i).comp (LinearMap.fst ℝ E ℝ)
  | Sum.inr false => -(LinearMap.snd ℝ E ℝ)
  | Sum.inr true => (1 / 2 : ℝ) • (LinearMap.snd ℝ E ℝ)



theorem cylinderUnitForms_ne_zero {ι : Type*} (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (i : ι ⊕ Bool) : cylinderUnitForms L i ≠ 0 := by
  intro h
  cases i with
  | inl i =>
    apply hL i
    ext x
    exact congrArg (fun M : (E × ℝ) →ₗ[ℝ] ℝ => M (x, 0)) h
  | inr i =>
    cases i <;>
      have he := congrArg (fun M : (E × ℝ) →ₗ[ℝ] ℝ => M (0, 2)) h <;>
      norm_num [cylinderUnitForms] at he



theorem cylinderUnitForms_region {ι : Type*} (L : ι → E →ₗ[ℝ] ℝ)
    {Q : Set E} (hQ : Q = {x | ∀ i, L i x ≤ 1}) :
    Q ×ˢ Icc (-1 : ℝ) 2 = {q | ∀ i, cylinderUnitForms L i q ≤ 1} := by
  ext q
  constructor
  · intro hq i
    cases i with
    | inl i =>
      exact (hQ.subset hq.1) i
    | inr i =>
      cases i
      · change -q.2 ≤ 1
        linarith [hq.2.1]
      · change (1 / 2 : ℝ) * q.2 ≤ 1
        linarith [hq.2.2]
  · intro hq
    refine ⟨hQ.symm.subset (fun i => hq (Sum.inl i)), ?_, ?_⟩
    · have h := hq (Sum.inr false)
      change -q.2 ≤ 1 at h
      linarith
    · have h := hq (Sum.inr true)
      change (1 / 2 : ℝ) * q.2 ≤ 1 at h
      linarith

end LinearMap
