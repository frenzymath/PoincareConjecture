import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryReflectedQuadraticGrowth

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Metric MeasureTheory Filter
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

theorem m64BoundaryReflect_sq {epsilon : ℝ} (he : epsilon ^ 2 = 1)
    (u : LoopPlane → ℝ) (p : LoopPlane) :
    m64BoundaryReflect epsilon u p ^ 2 =
      (halfSpace 2).indicator u p ^ 2 + (halfSpace 2).indicator u (reflect p) ^ 2 := by
  by_cases hp : p ∈ halfSpace 2
  · have hr : reflect p ∉ halfSpace 2 := by
      change ¬ 0 < (reflect p) 0
      rw [reflect_apply_zero]
      exact not_lt.mpr (neg_nonpos.mpr (show 0 < p 0 from hp).le)
    simp only [m64BoundaryReflect, indicator_of_notMem hr, mul_zero, add_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · simp only [m64BoundaryReflect, indicator_of_notMem hp, zero_add,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_pow, he, one_mul]

theorem m64BoundaryReflect_integral_sq {epsilon : ℝ} (he : epsilon ^ 2 = 1)
    {u : LoopPlane → ℝ} (hu : MemLp u 2 (volume.restrict (halfSpace 2)))
    (x : LoopPlane) (r : ℝ) :
    (∫ p in closedBall x r, m64BoundaryReflect epsilon u p ^ 2) =
      (∫ p in closedBall x r, (halfSpace 2).indicator u p ^ 2) +
        ∫ p in closedBall (reflect x) r, (halfSpace 2).indicator u p ^ 2 := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  have hI : Integrable (fun p => (halfSpace 2).indicator u p ^ 2) :=
    (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mp hi
  have hIR : Integrable (fun p => (halfSpace 2).indicator u (reflect p) ^ 2) :=
    measurePreserving_reflect.integrable_comp_of_integrable hI
  have hpre : reflect ⁻¹' closedBall (reflect x) r = closedBall x r := by
    ext p
    change dist (reflect p) (reflect x) ≤ r ↔ dist p x ≤ r
    rw [LinearIsometryEquiv.dist_map]
  simp_rw [m64BoundaryReflect_sq he]
  rw [integral_add hI.integrableOn hIR.integrableOn]
  congr 1
  rw [← hpre]
  exact (measurePreserving_reflect (d := 2)).setIntegral_preimage_emb
    reflect.toHomeomorph.measurableEmbedding
    (fun p : LoopPlane => (halfSpace 2).indicator u p ^ 2) (closedBall (reflect x) r)

theorem m64BoundaryReflect_integral_energy {N : ℕ}
    (epsilon : Fin N → ℝ) (he : ∀ j, epsilon j ^ 2 = 1)
    (V : Fin N → Fin 2 → LoopPlane → ℝ)
    (hV : ∀ j i, MemLp (V j i) 2 (volume.restrict (halfSpace 2)))
    (x : LoopPlane) (r : ℝ) :
    (∫ p in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2,
      m64BoundaryReflect (epsilon j * coordinateSign i) (V j i) p ^ 2) =
      (∫ p in closedBall x r, ∑ j : Fin N, ∑ i : Fin 2,
        (halfSpace 2).indicator (V j i) p ^ 2) +
      ∫ p in closedBall (reflect x) r, ∑ j : Fin N, ∑ i : Fin 2,
        (halfSpace 2).indicator (V j i) p ^ 2 := by
  have hsign (j : Fin N) (i : Fin 2) : (epsilon j * coordinateSign i) ^ 2 = 1 := by
    rw [mul_pow, he j]
    by_cases hi : i = 0 <;> simp [coordinateSign, hi]
  have hRI (j : Fin N) (i : Fin 2) : Integrable
      (fun p => m64BoundaryReflect (epsilon j * coordinateSign i) (V j i) p ^ 2) := by
    have h := m64BoundaryReflect_memLp (hV j i) (epsilon j * coordinateSign i)
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
  have hI (j : Fin N) (i : Fin 2) : Integrable
      (fun p => (halfSpace 2).indicator (V j i) p ^ 2) := by
    have h := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr (hV j i)
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun i _ => (hRI j i).integrableOn)),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun i _ => (hI j i).integrableOn)),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun i _ => (hI j i).integrableOn)), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun i _ => (hRI j i).integrableOn),
    integral_finsetSum _ (fun i _ => (hI j i).integrableOn),
    integral_finsetSum _ (fun i _ => (hI j i).integrableOn), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    m64BoundaryReflect_integral_sq (hsign j i) (hV j i) x r

end PoincareConjecture
