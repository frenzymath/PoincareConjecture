import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryReflectedEquation












noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory Metric
open scoped Topology
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture






theorem m64BoundaryReflect_quadratic_growth {N : ℕ} {R C : ℝ}
    (epsilon : Fin N → ℝ) (hepsilon : ∀ j, epsilon j ^ 2 = 1)
    (V : Fin N → Fin 2 → LoopPlane → ℝ) (b : Fin N → LoopPlane → ℝ)
    (hgrowth : ∀ j, ∀ᵐ p ∂volume.restrict (halfSpace 2), p ∈ ball 0 R →
      |b j p| ≤ C * ∑ k : Fin N, ∑ i : Fin 2, V k i p ^ 2) :
    ∀ j, ∀ᵐ p ∂volume, p ∈ ball 0 R →
      |m64BoundaryReflect (epsilon j) (b j) p| ≤
        C * ∑ k : Fin N, ∑ i : Fin 2,
          m64BoundaryReflect (epsilon k * coordinateSign i) (V k i) p ^ 2 := by
  have habs (j : Fin N) : |epsilon j| = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show epsilon j ^ 2 = (1 : ℝ) ^ 2 by simpa using hepsilon j) with hj | hj
    · rw [hj, abs_one]
    · rw [hj, abs_neg, abs_one]
  have hsign (j : Fin N) (i : Fin 2) : (epsilon j * coordinateSign i) ^ 2 = 1 := by
    rw [mul_pow, hepsilon j]
    by_cases hi : i = 0 <;> simp [coordinateSign, hi]
  intro j
  have hhalf := (ae_restrict_iff' isOpen_halfSpace.measurableSet).mp (hgrowth j)
  have href := measurePreserving_reflect.quasiMeasurePreserving.ae hhalf
  filter_upwards [hhalf, href] with p hp hr hpball
  by_cases hpH : p ∈ halfSpace 2
  · have hrH : reflect p ∉ halfSpace 2 := by
      change ¬ 0 < (reflect p) 0
      rw [reflect_apply_zero]
      exact not_lt.mpr (neg_nonpos.mpr (show 0 < p 0 from hpH).le)
    simpa only [m64BoundaryReflect, indicator_of_mem hpH, indicator_of_notMem hrH,
      mul_zero, add_zero] using hp hpH hpball
  · by_cases hrH : reflect p ∈ halfSpace 2
    · have hrball : reflect p ∈ ball (0 : LoopPlane) R := by
        simpa only [mem_ball_zero_iff, LinearIsometryEquiv.norm_map] using hpball
      have henergy :
          (∑ k : Fin N, ∑ i : Fin 2,
            m64BoundaryReflect (epsilon k * coordinateSign i) (V k i) p ^ 2) =
          ∑ k : Fin N, ∑ i : Fin 2, V k i (reflect p) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro i _
        simp only [m64BoundaryReflect, indicator_of_notMem hpH,
          indicator_of_mem hrH, zero_add]
        rw [mul_pow, hsign, one_mul]
      rw [henergy]
      simpa only [m64BoundaryReflect, indicator_of_notMem hpH,
        indicator_of_mem hrH, zero_add, abs_mul, habs, one_mul] using hr hrH hrball
    · simp only [m64BoundaryReflect, indicator_of_notMem hpH,
        indicator_of_notMem hrH, mul_zero, add_zero, abs_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, le_refl]

end PoincareConjecture
