import PoincareConjecture.Proofs.M76.Mathlib.ConvexRadialNormalization
import Mathlib.Data.Set.Card











set_option autoImplicit false

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem LinearMap.normalize_eq_zero_iff (A : E →ₗ[ℝ] ℝ) (x : E) :
    A (NormedSpace.normalize x) = 0 ↔ A x = 0 := by
  constructor
  · intro h
    have he := congrArg A (norm_smul_normalize x)
    rw [map_smul, h, smul_zero] at he
    exact he.symm
  · intro h
    simp only [NormedSpace.normalize, map_smul, h, smul_zero]




theorem LinearMap.normalize_pos_iff (A : E →ₗ[ℝ] ℝ) (x : E) :
    0 < A (NormedSpace.normalize x) ↔ 0 < A x := by
  by_cases hx : x = 0
  · simp only [hx, normalize_zero_eq_zero, map_zero]
  · rw [NormedSpace.normalize, map_smul, smul_eq_mul]
    exact mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hx))




theorem LinearMap.height_tests_of_normalize_eq (A : E →ₗ[ℝ] ℝ)
    {x y : E} (hxy : NormedSpace.normalize x = NormedSpace.normalize y) :
    (A x = 0 ↔ A y = 0) ∧ (0 < A x ↔ 0 < A y) ∧ (A x < 0 ↔ A y < 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← A.normalize_eq_zero_iff x, ← A.normalize_eq_zero_iff y, hxy]
  · rw [← A.normalize_pos_iff x, ← A.normalize_pos_iff y, hxy]
  · have h : 0 < (-A) x ↔ 0 < (-A) y := by
      rw [← (-A).normalize_pos_iff x, ← (-A).normalize_pos_iff y, hxy]
    simpa only [LinearMap.neg_apply, neg_pos] using h






theorem IsCompact.normalize_image_radial_frontier_section_inter
    {C S R : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hSzero : (0 : E) ∉ S)
    (hR : R = frontier C ∩ NormedSpace.normalize ⁻¹' (NormedSpace.normalize '' S))
    (P : E → Prop)
    (hP : ∀ {x y : E},
      NormedSpace.normalize x = NormedSpace.normalize y → (P x ↔ P y)) :
    NormedSpace.normalize '' (R ∩ {x | P x}) =
      NormedSpace.normalize '' (S ∩ {x | P x}) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (hR.subset hx.1).2
    exact ⟨y, ⟨hy, (hP hyx).mpr hx.2⟩, hyx⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hxC, hxy⟩ := hC.exists_frontier_normalize_eq hcv hzero
      (fun he => hSzero (he ▸ hy.1))
    exact ⟨x, ⟨hR.symm.subset ⟨hxC, y, hy.1, hxy.symm⟩,
      (hP hxy).mpr hy.2⟩, hxy⟩






theorem IsCompact.radial_frontier_section_height_data
    {C S R : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hSzero : (0 : E) ∉ S)
    (hrad : InjOn (NormedSpace.normalize : E → E) S)
    (hR : R = frontier C ∩ NormedSpace.normalize ⁻¹' (NormedSpace.normalize '' S))
    (A : E →ₗ[ℝ] ℝ) :
    (R ∩ {x | A x = 0}).ncard = (S ∩ {x | A x = 0}).ncard ∧
      ((∃ x ∈ R, A x < 0) ↔ ∃ x ∈ S, A x < 0) ∧
      ((∃ x ∈ R, 0 < A x) ↔ ∃ x ∈ S, 0 < A x) := by
  have htest (P : E → Prop)
      (hP : ∀ {x y : E},
        NormedSpace.normalize x = NormedSpace.normalize y → (P x ↔ P y)) :
      (∃ x ∈ R, P x) ↔ ∃ x ∈ S, P x := by
    have him := hC.normalize_image_radial_frontier_section_inter hcv hzero hSzero hR P hP
    constructor
    · rintro ⟨x, hx, hPx⟩
      obtain ⟨y, hy, _⟩ := him.subset ⟨x, ⟨hx, hPx⟩, rfl⟩
      exact ⟨y, hy.1, hy.2⟩
    · rintro ⟨y, hy, hPy⟩
      obtain ⟨x, hx, _⟩ := him.symm.subset ⟨y, ⟨hy, hPy⟩, rfl⟩
      exact ⟨x, hx.1, hx.2⟩
  refine ⟨?_, htest (fun x => A x < 0) (fun h => (A.height_tests_of_normalize_eq h).2.2),
    htest (fun x => 0 < A x) (fun h => (A.height_tests_of_normalize_eq h).2.1)⟩
  have hradR : InjOn (NormedSpace.normalize : E → E) (R ∩ {x | A x = 0}) :=
    (hcv.injOn_normalize_frontier hzero).mono
      (inter_subset_left.trans (hR.subset.trans inter_subset_left))
  have hradS : InjOn (NormedSpace.normalize : E → E) (S ∩ {x | A x = 0}) :=
    hrad.mono inter_subset_left
  rw [← hradR.ncard_image, ← hradS.ncard_image,
    hC.normalize_image_radial_frontier_section_inter hcv hzero hSzero hR
      (fun x => A x = 0) (fun h => (A.height_tests_of_normalize_eq h).1)]
