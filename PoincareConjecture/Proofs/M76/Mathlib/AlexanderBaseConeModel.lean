import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.TriangularRoof










set_option autoImplicit false

open Set Geometry

namespace AlexanderBaseConeModel



def lift : (ℝ × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
  (ContinuousAffineMap.id ℝ (ℝ × ℝ)).prod (ContinuousAffineMap.const ℝ (ℝ × ℝ) 1)



def top : Set ((ℝ × ℝ) × ℝ) := lift '' TriangularRoofModel.base



def rim : Set ((ℝ × ℝ) × ℝ) := lift '' frontier TriangularRoofModel.base



def solid : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 ≤ p.2 ∧ p.2 ≤ 1}



theorem isFinitePLBallPair_top : IsFinitePLBallPair (ℝ × ℝ) top rim :=
  TriangularRoofModel.isFinitePLBallPair_base.affine_image lift
    (fun _ _ _ _ h => congrArg Prod.fst h)



theorem height_top (p : ((ℝ × ℝ) × ℝ)) (hp : p ∈ top) : p.2 = 1 := by
  obtain ⟨x, _, rfl⟩ := hp
  rfl



theorem rim_nonempty : rim.Nonempty := by
  refine ⟨lift (0, 0), mem_image_of_mem lift ?_⟩
  rw [TriangularRoofModel.frontier_base]
  norm_num [TriangularRoofModel.roof]




theorem solid_eq_convexJoin : solid = convexJoin ℝ {0} top := by
  ext p
  rw [mem_convexJoin_zero_iff]
  constructor
  · rintro ⟨hx, hy, hsum, hz⟩
    have hz0 : 0 ≤ p.2 := by linarith
    by_cases hpz : p.2 = 0
    · have hpx : p.1.1 = 0 := by linarith
      have hpy : p.1.2 = 0 := by linarith
      have hbase : ((0, 0) : ℝ × ℝ) ∈ TriangularRoofModel.base := by
        rw [TriangularRoofModel.base_eq_triangle, TriangleDiskModel.mem_right_region_iff]
        norm_num
      refine ⟨lift (0, 0), mem_image_of_mem lift hbase, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      ext <;> simp [hpx, hpy, hpz]
    · let x : ℝ × ℝ := p.2⁻¹ • p.1
      have hbase : x ∈ TriangularRoofModel.base := by
        rw [TriangularRoofModel.base_eq_triangle, TriangleDiskModel.mem_right_region_iff]
        refine ⟨mul_nonneg (inv_nonneg.mpr hz0) hx,
          mul_nonneg (inv_nonneg.mpr hz0) hy, ?_⟩
        have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hz0)
        change p.2⁻¹ * p.1.1 + p.2⁻¹ * p.1.2 ≤ 1
        simpa only [mul_add, inv_mul_cancel₀ hpz] using h
      refine ⟨lift x, mem_image_of_mem lift hbase, p.2, ⟨hz0, hz⟩, ?_⟩
      apply Prod.ext
      · change p.1 = p.2 • (p.2⁻¹ • p.1)
        rw [smul_inv_smul₀ hpz]
      · change p.2 = p.2 * 1
        ring
  · rintro ⟨_, ⟨x, hx, rfl⟩, r, hr, rfl⟩
    rw [TriangularRoofModel.base_eq_triangle, TriangleDiskModel.mem_right_region_iff] at hx
    change 0 ≤ r * x.1 ∧ 0 ≤ r * x.2 ∧ r * x.1 + r * x.2 ≤ r * 1 ∧ r * 1 ≤ 1
    exact ⟨mul_nonneg hr.1 hx.1, mul_nonneg hr.1 hx.2.1,
      by nlinarith [mul_le_mul_of_nonneg_left hx.2.2 hr.1], by simpa using hr.2⟩



def forms : Fin 4 → ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ℝ :=
  let x := ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let y := ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let z := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  ![-x, -y, x + y - z, z - AffineMap.const ℝ ((ℝ × ℝ) × ℝ) 1]



theorem solid_eq_halfspaces : solid = {p | ∀ i, forms i p ≤ 0} := by
  ext p
  simp only [solid, forms, mem_ofPred_eq, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  change (0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ p.1.1 + p.1.2 ≤ p.2 ∧ p.2 ≤ 1) ↔
    (-p.1.1 ≤ 0 ∧ -p.1.2 ≤ 0 ∧ p.1.1 + p.1.2 - p.2 ≤ 0 ∧ p.2 - 1 ≤ 0)
  constructor <;> rintro ⟨hx, hy, hsum, hz⟩ <;> exact ⟨by linarith, by linarith,
    by linarith, by linarith⟩



theorem forms_linear_ne_zero (i : Fin 4) : (forms i).linear ≠ 0 := by
  intro hzero
  have h := LinearMap.congr_fun hzero (((1, 1), 1) : (ℝ × ℝ) × ℝ)
  fin_cases i <;> norm_num [forms] at h


theorem isClosed_solid : IsClosed solid := by
  rw [solid_eq_halfspaces]
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (forms i).continuous_of_finiteDimensional
    continuous_const



theorem interior_solid : interior solid =
    {p | 0 < p.1.1 ∧ 0 < p.1.2 ∧ p.1.1 + p.1.2 < p.2 ∧ p.2 < 1} := by
  rw [solid_eq_halfspaces, interior_finite_affine_halfspaces _ forms_linear_ne_zero]
  ext p
  simp only [forms, mem_ofPred_eq, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.forall_fin_zero, and_true]
  change (-p.1.1 < 0 ∧ -p.1.2 < 0 ∧ p.1.1 + p.1.2 - p.2 < 0 ∧ p.2 - 1 < 0) ↔
    (0 < p.1.1 ∧ 0 < p.1.2 ∧ p.1.1 + p.1.2 < p.2 ∧ p.2 < 1)
  constructor <;> rintro ⟨hx, hy, hsum, hz⟩ <;> exact ⟨by linarith, by linarith,
    by linarith, by linarith⟩



theorem isCompact_solid : IsCompact solid := by
  have hc : IsCompact (Icc (((0, 0), 0) : (ℝ × ℝ) × ℝ) ((1, 1), 1)) := isCompact_Icc
  apply hc.of_isClosed_subset isClosed_solid
  rintro p ⟨hx, hy, hsum, hz⟩
  exact ⟨⟨⟨hx, hy⟩, by linarith⟩, ⟨⟨by linarith, by linarith⟩, hz⟩⟩



theorem interior_solid_nonempty : (interior solid).Nonempty := by
  refine ⟨((1 / 8, 1 / 8), 1 / 2), ?_⟩
  rw [interior_solid]
  norm_num




theorem frontier_solid : frontier solid = top ∪ convexJoin ℝ {0} rim := by
  rw [frontier, isClosed_solid.closure_eq, interior_solid]
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    rw [solid_eq_convexJoin, mem_convexJoin_zero_iff] at hp
    obtain ⟨_, ⟨x, hx, rfl⟩, r, hr, rfl⟩ := hp
    by_cases hr0 : r = 0
    · right
      obtain ⟨z, hz⟩ := rim_nonempty
      exact (mem_convexJoin_zero_iff _ _).mpr ⟨z, hz, 0, ⟨le_rfl, zero_le_one⟩,
        by simp [hr0]⟩
    · by_cases hr1 : r = 1
      · left
        change r • lift x ∈ lift '' TriangularRoofModel.base
        simpa only [hr1, one_smul] using mem_image_of_mem lift hx
      · right
        have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
        have hrlt : r < 1 := lt_of_le_of_ne hr.2 hr1
        have hroof : TriangularRoofModel.roof x = 0 := by
          apply le_antisymm _ ((TriangularRoofModel.roof_nonneg_iff x).mpr hx)
          by_contra h
          have hpos : 0 < TriangularRoofModel.roof x := lt_of_not_ge h
          simp only [TriangularRoofModel.roof, lt_min_iff] at hpos
          apply hn
          change 0 < r * x.1 ∧ 0 < r * x.2 ∧ r * x.1 + r * x.2 < r * 1 ∧ r * 1 < 1
          exact ⟨mul_pos hrpos hpos.1, mul_pos hrpos hpos.2.1,
            by nlinarith [mul_pos hrpos hpos.2.2], by simpa using hrlt⟩
        have hxrim : lift x ∈ rim := mem_image_of_mem lift (by
          rw [TriangularRoofModel.frontier_base]
          exact hroof)
        exact (mem_convexJoin_zero_iff _ _).mpr ⟨lift x, hxrim, r, hr, rfl⟩
  · intro hp
    have hrt : rim ⊆ top := isFinitePLBallPair_top.1
    have hpS : p ∈ solid := by
      rw [solid_eq_convexJoin]
      rcases hp with hp | hp
      · exact (mem_convexJoin_zero_iff _ _).mpr ⟨p, hp, 1, ⟨zero_le_one, le_rfl⟩,
          by simp⟩
      · obtain ⟨y, hy, r, hr, hpr⟩ := (mem_convexJoin_zero_iff _ _).mp hp
        exact (mem_convexJoin_zero_iff _ _).mpr ⟨y, hrt hy, r, hr, hpr⟩
    refine ⟨hpS, ?_⟩
    intro hi
    rcases hp with hp | hp
    · exact (ne_of_lt hi.2.2.2) (height_top p hp)
    · obtain ⟨_, ⟨x, hx, rfl⟩, r, hr, rfl⟩ := (mem_convexJoin_zero_iff _ _).mp hp
      have hxroof : TriangularRoofModel.roof x = 0 := by
        rwa [TriangularRoofModel.frontier_base] at hx
      change 0 < r * x.1 ∧ 0 < r * x.2 ∧ r * x.1 + r * x.2 < r * 1 ∧ r * 1 < 1 at hi
      have hrpos : 0 < r := by
        by_contra hn
        have hr0 : r = 0 := le_antisymm (not_lt.mp hn) hr.1
        simp [hr0] at hi
      have hxpos : 0 < TriangularRoofModel.roof x := by
        simp only [TriangularRoofModel.roof, lt_min_iff]
        exact ⟨by nlinarith [hi.1], by nlinarith [hi.2.1],
          by nlinarith [hi.2.2.1]⟩
      exact hxpos.ne' hxroof




theorem isFinitePLBallPair_cone : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
    (convexJoin ℝ {0} top) (top ∪ convexJoin ℝ {0} rim) := by
  classical
  let H := Finset.univ.image forms
  have hrep : solid = {p | ∀ A ∈ H, A p ≤ 0} := by
    rw [solid_eq_halfspaces]
    ext p
    simp [H]
  have h := isFinitePLBallPair_of_affine_halfspaces isCompact_solid H hrep
    interior_solid_nonempty
  rwa [frontier_solid, solid_eq_convexJoin] at h

end AlexanderBaseConeModel
