import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.WeakDerivatives
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryLocalization

open Weak Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integral_inter_eq {W O : Set E} (hW : IsOpen W) {v : E → ℝ}
    (hv : ∀ x, x ∉ W → v x = 0) :
    (∫ x in W ∩ O, v x) = ∫ x in O, v x := by
  rw [← Measure.restrict_restrict hW.measurableSet]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hv

private theorem memLp_mul_smooth_extend {W O : Set E} (hW : IsOpen W)
    {u χ : E → ℝ} (hu : MemLp u 2 (volume.restrict (W ∩ O)))
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W) :
    MemLp (fun x => χ x * u x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hχ.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hm : MemLp (fun x => χ x * u x) 2 (volume.restrict (W ∩ O)) := by
    apply hu.of_le_mul (c := C) (hχ.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC ⟨x, rfl⟩) (norm_nonneg _)
  have hext : MemLp (W.indicator (fun x => χ x * u x)) 2 (volume.restrict O) :=
    (memLp_indicator_iff_restrict hW.measurableSet).mpr
    (show MemLp (fun x => χ x * u x) 2 ((volume.restrict O).restrict W) by
      simpa only [Measure.restrict_restrict hW.measurableSet] using hm)
  have heq : W.indicator (fun x => χ x * u x) = fun x => χ x * u x := by
    funext x
    by_cases hx : x ∈ W
    · simp [hx]
    · simp [hx, image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))]
  rwa [heq] at hext

theorem hasWeakPartialDeriv_mul_smooth_of_tsupport_subset
    {W O : Set E} (hW : IsOpen W)
    {u g χ : E → ℝ} (i : Fin d)
    (hu : MemLp u 2 (volume.restrict (W ∩ O)))
    (hg : MemLp g 2 (volume.restrict (W ∩ O)))
    (hw : HasWeakPartialDeriv i g u (W ∩ O))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W) :
    HasWeakPartialDeriv i
      (fun x => χ x * g x + fderiv ℝ χ x (EuclideanSpace.single i 1) * u x)
      (fun x => χ x * u x) O := by
  intro φ hφ hφc hφs
  let Dχ (x : E) := fderiv ℝ χ x (EuclideanSpace.single i 1)
  let Dφ (x : E) := fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hDχ : Continuous Dχ := (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDφ : Continuous Dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχzero (x : E) (hx : x ∉ W) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
  have hDχzero (x : E) (hx : x ∉ W) : Dχ x = 0 := by
    dsimp only [Dχ]
    rw [fderiv_of_notMem_tsupport ℝ (fun ht => hx (hs ht))]
    simp
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict O
  have hDφLp : MemLp Dφ 2 (volume.restrict O) :=
    (hDφ.memLp_of_hasCompactSupport (hφc.fderiv_apply ℝ _)).restrict O
  have hχu := memLp_mul_smooth_extend hW hu hχ.continuous hc hs
  have hχg := memLp_mul_smooth_extend hW hg hχ.continuous hc hs
  have hDχu := memLp_mul_smooth_extend hW hu hDχ (hc.fderiv_apply ℝ _)
    ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have htest := hw (fun x => χ x * φ x) (hχ.mul hφ) hc.mul_right
    (fun x hx => ⟨hs (tsupport_mul_subset_left hx), hφs (tsupport_mul_subset_right hx)⟩)
  have hleft : (∫ x in W ∩ O, u x *
      fderiv ℝ (fun y => χ y * φ y) x (EuclideanSpace.single i 1)) =
      ∫ x in W ∩ O, χ x * u x * Dφ x + Dχ x * u x * φ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [fderiv_fun_mul (hχ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      dsimp only [Dχ, Dφ]
      ring
  have hright : (∫ x in W ∩ O, g x * (χ x * φ x)) =
      ∫ x in W ∩ O, χ x * g x * φ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [hleft, hright] at htest
  have hleftExtend : (∫ x in W ∩ O, χ x * u x * Dφ x + Dχ x * u x * φ x) =
      ∫ x in O, χ x * u x * Dφ x + Dχ x * u x * φ x :=
    integral_inter_eq hW (fun x hx => by rw [hχzero x hx, hDχzero x hx]; ring)
  have hrightExtend : (∫ x in W ∩ O, χ x * g x * φ x) =
      ∫ x in O, χ x * g x * φ x :=
    integral_inter_eq hW (fun x hx => by rw [hχzero x hx]; ring)
  rw [hleftExtend, hrightExtend] at htest
  have hsplitL := integral_add (hχu.integrable_mul hDφLp) (hDχu.integrable_mul hφLp)
  have hsplitR := integral_add (hχg.integrable_mul hφLp) (hDχu.integrable_mul hφLp)
  simp only [Pi.mul_apply] at hsplitL hsplitR
  rw [hsplitL] at htest
  change (∫ x in O, χ x * u x * Dφ x) =
    -(∫ x in O, (χ x * g x + Dχ x * u x) * φ x)
  simp_rw [add_mul]
  rw [hsplitR]
  linarith

theorem memWkp_mul_smooth_of_tsupport_subset
    (k : ℕ) {O W : Set E} (hO : IsOpen O) (hW : IsOpen W)
    {u χ : E → ℝ} (hu : MemWkp k 2 u (W ∩ O))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W) :
    MemWkp k 2 (fun x => χ x * u x) O := by
  induction k generalizing u χ with
  | zero => exact memLp_mul_smooth_extend hW hu hχ.continuous hc hs
  | succ k ih =>
    apply memWkp_succ_of_weakDerivatives hO (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (g := fun i x => χ x * chosenWeakPartial' 2 i u (W ∩ O) x +
        fderiv ℝ χ x (EuclideanSpace.single i 1) * u x)
      (memLp_mul_smooth_extend hW hu.memLp hχ.continuous hc hs)
    · intro i
      have hDχ : ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (EuclideanSpace.single i 1)) :=
        (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      exact MemWkp.add (by norm_num) hO
        (ih (hu.chosenWeakPartial_mem i) hχ hc hs)
        (ih hu.le_succ hDχ (hc.fderiv_apply ℝ _)
          ((tsupport_fderiv_apply_subset ℝ _).trans hs))
    · intro i
      exact hasWeakPartialDeriv_mul_smooth_of_tsupport_subset hW i hu.memLp
        (chosenWeakPartial'_memLp_of_mem hu.memW1p i)
        (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i) hχ hc hs

theorem memWkp_mul_smooth_of_isCompact_closure
    (k : ℕ) {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {u a : E → ℝ} (hu : MemWkp k 2 u O) (ha : ContDiff ℝ ∞ a) :
    MemWkp k 2 (fun x => a x * u x) O := by
  obtain ⟨χ, hχ, hc, _, hone, _⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hOc isOpen_univ (subset_univ _)
  have hm := memWkp_mul_smooth_of_tsupport_subset k hO isOpen_univ
    (by simpa only [univ_inter] using hu) (hχ.mul ha) hc.mul_right (subset_univ _)
  apply (MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO _).mp hm
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [hone x (subset_closure hx), one_mul]

end Poincare.Analysis.Sobolev.BoundaryLocalization
