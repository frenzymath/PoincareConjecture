import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryInverseMetric

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped ContDiff

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64BoundaryInverseCoefficientBounds_bilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryInverseCoefficientBounds_bilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64BoundaryInverseCoefficientBounds_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryInverseCoefficientBounds_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem m64BoundaryMetric_inverse_coefficient_bounds
    {U K : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hG : ContDiffOn ℝ ∞ G U)
    (hpos : ∀ z ∈ U, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < G z v v) :
    ∃ L : ℝ, 0 < L ∧ ∀ z ∈ K, ‖G z‖ ≤ L ∧ ‖fderiv ℝ G z‖ ≤ L ∧
      ∀ k j : Fin n,
        |(m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) j| ≤ L ∧
        ‖fderiv ℝ (fun y =>
          (m64BoundaryMetricInverse (G y) (EuclideanSpace.single k 1)) j) z‖ ≤ L := by
  let A : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun k j z =>
    (m64BoundaryMetricInverse (G z) (EuclideanSpace.single k 1)) j
  have hA (k j : Fin n) : ContDiffOn ℝ ∞ (A k j) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn
      ((m64BoundaryMetricInverse_smooth hG hpos).clm_apply contDiffOn_const)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn (hG.continuousOn.mono hKU)
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn
    ((hG.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU)
  have hbound (k j : Fin n) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K,
      |A k j z| ≤ B ∧ ‖fderiv ℝ (A k j) z‖ ≤ B := by
    obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn ((hA k j).continuousOn.mono hKU)
    obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn
      (((hA k j).continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU)
    refine ⟨|B0| + |B1|, by positivity, fun z hz => ⟨?_, ?_⟩⟩
    · have hh := hB0 z hz
      rw [Real.norm_eq_abs] at hh
      linarith [le_abs_self B0, abs_nonneg B1]
    · linarith [hB1 z hz, le_abs_self B1, abs_nonneg B0]
  choose B hB hBb using hbound
  let D := ∑ k : Fin n, ∑ j : Fin n, B k j
  have hD : 0 ≤ D := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => hB k j
  have hBD (k j : Fin n) : B k j ≤ D := by
    exact (Finset.single_le_sum (fun l _ => hB k l) (Finset.mem_univ j)).trans
      (Finset.single_le_sum
        (fun l _ => Finset.sum_nonneg fun a _ => hB l a) (Finset.mem_univ k))
  let L := 1 + |C0| + |C1| + D
  have hDL : D ≤ L := by
    dsimp only [L]
    linarith [abs_nonneg C0, abs_nonneg C1]
  refine ⟨L, by dsimp only [L]; positivity, fun z hz => ⟨?_, ?_, ?_⟩⟩
  · have hh := hC0 z hz
    dsimp only [L]
    linarith [le_abs_self C0, abs_nonneg C1]
  · have hh := hC1 z hz
    dsimp only [L]
    linarith [le_abs_self C1, abs_nonneg C0]
  · intro k j
    exact ⟨((hBb k j z hz).1.trans (hBD k j)).trans hDL,
      ((hBb k j z hz).2.trans (hBD k j)).trans hDL⟩

end PoincareConjecture
