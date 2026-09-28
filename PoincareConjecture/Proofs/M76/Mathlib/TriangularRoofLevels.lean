import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskRoof
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

def levelContraction (t : ℝ) : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
  (1 - 3 * t) • ContinuousAffineMap.id ℝ (ℝ × ℝ) +
    ContinuousAffineMap.const ℝ (ℝ × ℝ) (t, t)

theorem levelContraction_apply (t : ℝ) (p : ℝ × ℝ) :
    levelContraction t p = ((1 - 3 * t) * p.1 + t, (1 - 3 * t) * p.2 + t) := rfl

theorem roof_levelContraction {t : ℝ} (ht : t ≤ 1 / 3) (p : ℝ × ℝ) :
    roof (levelContraction t p) = (1 - 3 * t) * roof p + t := by
  have hc : 0 ≤ 1 - 3 * t := by linarith
  simp only [roof, levelContraction_apply]
  have hthird : 1 - ((1 - 3 * t) * p.1 + t) - ((1 - 3 * t) * p.2 + t) =
      (1 - 3 * t) * (1 - p.1 - p.2) + t := by ring
  rw [hthird, mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc]
  simp only [min_add_add_right]

theorem bijective_levelContraction {t : ℝ} (ht : t < 1 / 3) :
    Function.Bijective (levelContraction t) := by
  have hc : 1 - 3 * t ≠ 0 := by linarith
  constructor
  · intro p q hpq
    have h1 := congrArg Prod.fst hpq
    have h2 := congrArg Prod.snd hpq
    simp only [levelContraction_apply] at h1 h2
    exact Prod.ext (mul_left_cancel₀ hc (add_right_cancel h1))
      (mul_left_cancel₀ hc (add_right_cancel h2))
  · intro p
    refine ⟨((p.1 - t) / (1 - 3 * t), (p.2 - t) / (1 - 3 * t)), ?_⟩
    apply Prod.ext <;> simp only [levelContraction_apply] <;> field_simp <;> ring

theorem levelContraction_image_base {t : ℝ} (ht : t < 1 / 3) :
    levelContraction t '' base = {p | t ≤ roof p} := by
  have hc : 0 < 1 - 3 * t := by linarith
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change t ≤ roof (levelContraction t q)
    rw [roof_levelContraction ht.le]
    have hq' := (roof_nonneg_iff q).mpr hq
    nlinarith
  · intro hp
    obtain ⟨q, rfl⟩ := (bijective_levelContraction ht).surjective p
    change t ≤ roof (levelContraction t q) at hp
    rw [roof_levelContraction ht.le] at hp
    exact ⟨q, (roof_nonneg_iff q).mp (by nlinarith), rfl⟩

theorem levelContraction_image_frontier {t : ℝ} (ht : t < 1 / 3) :
    levelContraction t '' frontier base = {p | roof p = t} := by
  have hc : 0 < 1 - 3 * t := by linarith
  rw [frontier_base]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change roof (levelContraction t q) = t
    rw [roof_levelContraction ht.le, hq, mul_zero, zero_add]
  · intro hp
    obtain ⟨q, rfl⟩ := (bijective_levelContraction ht).surjective p
    change roof (levelContraction t q) = t at hp
    rw [roof_levelContraction ht.le] at hp
    exact ⟨q, by change roof q = 0; nlinarith, rfl⟩

theorem isFinitePLBallPair_roof_superlevel {t : ℝ} (ht : t < 1 / 3) :
    IsFinitePLBallPair (ℝ × ℝ) {p | t ≤ roof p} {p | roof p = t} := by
  rw [← levelContraction_image_base ht, ← levelContraction_image_frontier ht]
  exact isFinitePLBallPair_base.affine_image (levelContraction t)
    (bijective_levelContraction ht).injective.injOn

theorem roof_superlevel_subset_base {t : ℝ} (ht : 0 ≤ t) :
    {p | t ≤ roof p} ⊆ base :=
  fun p hp => (roof_nonneg_iff p).mp (ht.trans hp)

theorem roof_superlevel_max :
    {p : ℝ × ℝ | 1 / 3 ≤ roof p} = {(1 / 3, 1 / 3)} := by
  ext p
  exact ⟨fun hp => (roof_eq_third_iff p).mp (le_antisymm (roof_le_third p) hp),
    fun hp => ((roof_eq_third_iff p).mpr hp).ge⟩

theorem roof_superlevel_eq_empty {t : ℝ} (ht : 1 / 3 < t) :
    {p : ℝ × ℝ | t ≤ roof p} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (not_lt_of_ge (hp.trans (roof_le_third p))) ht

end TriangularRoofModel
