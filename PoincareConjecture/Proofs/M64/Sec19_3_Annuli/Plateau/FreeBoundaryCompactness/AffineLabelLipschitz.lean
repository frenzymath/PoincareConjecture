import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.LiftNormalization
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz












set_option autoImplicit false

open Set
open scoped Topology NNReal

namespace PoincareConjecture.M64




theorem monotone_period_shift_lipschitz_of_locallyLipschitz
    {sigma : ℝ → ℝ} {P : ℝ} (hP : 0 < P) (hm : Monotone sigma)
    (hp : ∀ x, sigma (x + P) = sigma x + P)
    (hlocal : LocallyLipschitz sigma) : ∃ K : ℝ≥0, LipschitzWith K sigma := by
  obtain ⟨C, hC⟩ := hlocal.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * P)))
  have hperiod : Function.Periodic (fun x => sigma x - x) P := by
    intro x
    change sigma (x + P) - (x + P) = sigma x - x
    rw [hp]
    ring
  have htranslate (x : ℝ) (k : ℤ) :
      sigma (x - (k : ℝ) * P) = sigma x - (k : ℝ) * P := by
    have h := hperiod.sub_int_mul_eq (x := x) k
    linarith
  have hnormalize (x : ℝ) : sigma x - sigma 0 ∈ Icc (x - P) (x + 2 * P) := by
    apply monotone_period_shift_bounds hP
      (show Monotone (fun x => sigma x - sigma 0) from
        fun _ _ h => sub_le_sub_right (hm h) _)
      (fun x => by rw [hp]; ring)
    simpa using hP.le
  have hforward (x y : ℝ) (hxy : x ≤ y) :
      |sigma x - sigma y| ≤ (max C 4 : ℝ≥0) * |x - y| := by
    by_cases hsmall : y - x ≤ P
    · let k : ℤ := ⌊x / P⌋
      have hlo : (k : ℝ) * P ≤ x := (le_div_iff₀ hP).mp (Int.floor_le (x / P))
      have hhi : x < ((k : ℝ) + 1) * P :=
        (div_lt_iff₀ hP).mp (Int.lt_floor_add_one (x / P))
      have hx : x - (k : ℝ) * P ∈ Icc (0 : ℝ) (2 * P) :=
        ⟨by linarith, by nlinarith⟩
      have hy : y - (k : ℝ) * P ∈ Icc (0 : ℝ) (2 * P) :=
        ⟨by linarith, by nlinarith⟩
      have hpair := hC.dist_le_mul _ hx _ hy
      simp only [Real.dist_eq, htranslate, sub_sub_sub_cancel_right] at hpair
      exact hpair.trans (mul_le_mul_of_nonneg_right
        (show (C : ℝ) ≤ (max C 4 : ℝ≥0) from by exact_mod_cast le_max_left C 4)
        (abs_nonneg _))
    · have hx := hnormalize x
      have hy := hnormalize y
      have hfar : P < y - x := lt_of_not_ge hsmall
      rw [abs_of_nonpos (sub_nonpos.mpr (hm hxy)), abs_of_nonpos (sub_nonpos.mpr hxy)]
      have hfour : sigma y - sigma x ≤ 4 * (y - x) := by
        linarith [hx.1, hy.2]
      have hmax : (4 : ℝ) ≤ (max C 4 : ℝ≥0) := by exact_mod_cast le_max_right C 4
      nlinarith
  refine ⟨max C 4, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simp only [Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · exact hforward x y hxy
  · simpa only [abs_sub_comm] using hforward y x hyx

end PoincareConjecture.M64
