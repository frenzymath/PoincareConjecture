import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.SecondDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.Nirenberg











noncomputable section

open Set MeasureTheory
open scoped ENNReal
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_weakPartial_eLpNorm_le_of_integral_diffQuot_bound
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {p : Fin d → E → ℝ} (hp : ∀ i, MemLp (p i) 2 volume)
    {h₀ : ℝ} (hh₀ : 0 < h₀) {C : Fin d → ℝ}
    (hbound : ∀ k : Fin d, ∀ h : ℝ, h ≠ 0 → |h| ≤ h₀ →
      (∫ x in V, ∑ i, diffQuot k h (p i) x ^ 2) ≤ C k)
    (i k : Fin d) :
    ∃ q : E → ℝ, MemLp q 2 (volume.restrict V) ∧
      HasWeakPartialDeriv k q (p i) V ∧
      eLpNorm q 2 (volume.restrict V) ≤ ENNReal.ofReal (Real.sqrt (C k)) := by
  have hb (h : ℝ) (hh : 0 < |h|) (hle : |h| ≤ h₀) :
      eLpNorm (diffQuot k h (p i)) 2 (volume.restrict V) ≤
        ENNReal.ofReal (Real.sqrt (C k)) := by
    have hq (j : Fin d) := (memLp_diffQuot_two k h (hp j)).restrict V
    have hsq (j : Fin d) : Integrable (fun x => diffQuot k h (p j) x ^ 2)
        (volume.restrict V) := by
      simpa only [pow_two, Pi.mul_def] using (hq j).integrable_mul (hq j)
    apply eLpNorm_two_le_sqrt_of_integral_sq_le (hq i)
    apply le_trans _ (hbound k h (abs_pos.mp hh) hle)
    apply integral_mono (hsq i)
      (integrable_finsetSum _ (fun j _ => hsq j))
    intro x
    exact Finset.single_le_sum (fun j _ => sq_nonneg (diffQuot k h (p j) x))
      (Finset.mem_univ i)
  exact hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc isOpen_univ hV hVc hh₀
    (subset_univ _) (by simpa using hp i) k (Real.sqrt_nonneg (C k)) hb

theorem classicalPartial_eLpNorm_le_of_integral_diffQuot_bound
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {p : Fin d → E → ℝ} (hp : ∀ i, MemLp (p i) 2 volume)
    (hp_smooth : ∀ i, ContDiff ℝ 1 (p i))
    {h₀ : ℝ} (hh₀ : 0 < h₀) {C : Fin d → ℝ}
    (hbound : ∀ k : Fin d, ∀ h : ℝ, h ≠ 0 → |h| ≤ h₀ →
      (∫ x in V, ∑ i, diffQuot k h (p i) x ^ 2) ≤ C k)
    (i k : Fin d) :
    MemLp (fun x => fderiv ℝ (p i) x (EuclideanSpace.single k 1)) 2
        (volume.restrict V) ∧
      eLpNorm (fun x => fderiv ℝ (p i) x (EuclideanSpace.single k 1)) 2
        (volume.restrict V) ≤ ENNReal.ofReal (Real.sqrt (C k)) := by
  obtain ⟨q, hq, hweak, hnorm⟩ :=
    exists_weakPartial_eLpNorm_le_of_integral_diffQuot_bound hV hVc hp hh₀ hbound i k
  have hclassical := HasWeakPartialDeriv.of_contDiff (i := k) hV (hp_smooth i)
  have hcont : Continuous (fun x => fderiv ℝ (p i) x (EuclideanSpace.single k 1)) :=
    ((hp_smooth i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have heq := HasWeakPartialDeriv.ae_eq hV hweak hclassical
    (hq.locallyIntegrable (by norm_num))
    (hcont.locallyIntegrable.mono_measure Measure.restrict_le_self)
  refine ⟨hq.ae_eq heq, ?_⟩
  rw [← eLpNorm_congr_ae heq]
  exact hnorm

theorem classicalPartial_integral_sq_le_of_integral_diffQuot_bound
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {p : Fin d → E → ℝ} (hp : ∀ i, MemLp (p i) 2 volume)
    (hp_smooth : ∀ i, ContDiff ℝ 1 (p i))
    {h₀ : ℝ} (hh₀ : 0 < h₀) {C : Fin d → ℝ} (hC : ∀ k, 0 ≤ C k)
    (hbound : ∀ k : Fin d, ∀ h : ℝ, h ≠ 0 → |h| ≤ h₀ →
      (∫ x in V, ∑ i, diffQuot k h (p i) x ^ 2) ≤ C k)
    (i k : Fin d) :
    (∫ x in V, (fderiv ℝ (p i) x (EuclideanSpace.single k 1)) ^ 2) ≤ C k := by
  obtain ⟨hm, hn⟩ := classicalPartial_eLpNorm_le_of_integral_diffQuot_bound
    hV hVc hp hp_smooth hh₀ hbound i k
  have hn' := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hn
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hn'
  rw [← eLpNorm_toReal_sq_eq_integral hm, ← Real.sq_sqrt (hC k)]
  exact (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mpr hn'

theorem classicalGradient_integral_sq_le_of_integral_diffQuot_bound
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {p : Fin d → E → ℝ} (hp : ∀ i, MemLp (p i) 2 volume)
    (hp_smooth : ∀ i, ContDiff ℝ 1 (p i))
    {h₀ : ℝ} (hh₀ : 0 < h₀) {C : Fin d → ℝ} (hC : ∀ k, 0 ≤ C k)
    (hbound : ∀ k : Fin d, ∀ h : ℝ, h ≠ 0 → |h| ≤ h₀ →
      (∫ x in V, ∑ i, diffQuot k h (p i) x ^ 2) ≤ C k) :
    (∫ x in V, ∑ k : Fin d, ∑ i : Fin d,
      (fderiv ℝ (p i) x (EuclideanSpace.single k 1)) ^ 2) ≤
        (d : ℝ) * ∑ k : Fin d, C k := by
  have hint (i k : Fin d) : Integrable
      (fun x => (fderiv ℝ (p i) x (EuclideanSpace.single k 1)) ^ 2)
      (volume.restrict V) :=
    (classicalPartial_eLpNorm_le_of_integral_diffQuot_bound
      hV hVc hp hp_smooth hh₀ hbound i k).1.integrable_sq
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => hint i k))]
  calc
    _ ≤ ∑ k : Fin d, ∑ _i : Fin d, C k := by
      apply Finset.sum_le_sum
      intro k _
      rw [integral_finsetSum _ (fun i _ => hint i k)]
      exact Finset.sum_le_sum (fun i _ =>
        classicalPartial_integral_sq_le_of_integral_diffQuot_bound
          hV hVc hp hp_smooth hh₀ hC hbound i k)
    _ = _ := by simp [Finset.mul_sum]




theorem classicalPartial_integral_sq_le_nirenberg
    [NeZero d] {Ω V : Set E} (B : NirenbergEuclidean.SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 volume) (hf : MemLp f 2 volume)
    (hp : ∀ i, MemLp (p i) 2 volume)
    (hp_smooth : ∀ i, ContDiff ℝ 1 (p i))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u univ)
    (hF : ∀ j, MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x) 2 volume)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∫ x in V, ∑ j : Fin d,
        (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in V, f x * φ x)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηrange : range η ⊆ Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (hDη : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set E} (hΩ' : IsOpen Ω') (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ'c : IsCompact (closure Ω')) (hΩ'V : Ω' ⊆ V)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hthick : ∀ {h : ℝ}, |h| ≤ R₀ → Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hηone : ∀ x ∈ Ω'', η x = 1)
    (hΩ'' : IsOpen Ω'') (hΩ''c : IsCompact (closure Ω'')) (i k : Fin d) :
    (∫ x in Ω'', (fderiv ℝ (p i) x (EuclideanSpace.single k 1)) ^ 2) ≤
      (2 * nirenbergMasterYoungConstant B N hΩ'c k / B.lam) *
        ((∫ x in Ω', ∑ i : Fin d, (p i x) ^ 2) +
          (∫ x in Ω', (u x) ^ 2) + (∫ x in Ω', (f x) ^ 2)) := by
  let energy : ℝ := (∫ x in Ω', ∑ i : Fin d, (p i x) ^ 2) +
    (∫ x in Ω', (u x) ^ 2) + (∫ x in Ω', (f x) ^ 2)
  have henergy : 0 ≤ energy := by
    dsimp [energy]
    positivity
  apply classicalPartial_integral_sq_le_of_integral_diffQuot_bound hΩ'' hΩ''c hp
    hp_smooth hR₀ (C := fun k =>
      (2 * nirenbergMasterYoungConstant B N hΩ'c k / B.lam) * energy) ?_ ?_ i k
  · intro k
    exact mul_nonneg (div_nonneg
      (mul_nonneg (by norm_num) (nirenbergMasterYoungConstant_nonneg B hN hΩ'c k))
      B.hlam_pos.le) henergy
  · intro k h hh hhle
    have hestimate := diffQuot_weakGradient_localL2_bound_quantitative B hV hu hf hp hw hF heq
      hη hηc hηrange hN hDη hΩ' hΩ'Ω hΩ'c hΩ'V hR₀ hthick hηone
      hΩ''.measurableSet k hh hhle
    rw [mul_comm (B.lam / 2)] at hestimate
    have h' := (le_div_iff₀
      (div_pos B.hlam_pos (by norm_num : (0 : ℝ) < 2))).mpr hestimate
    calc
      _ ≤ nirenbergMasterYoungConstant B N hΩ'c k * energy / (B.lam / 2) := h'
      _ = _ := by rw [div_div_eq_mul_div]; ring

end Poincare.Analysis.Elliptic.InteriorEstimates
