import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.SecondDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.Localization













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ENNReal ContDiff

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)




theorem suWeak_hessian_integral_le
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ} {p : Fin d → E → ℝ},
      MemLp u 2 volume → MemLp f 2 volume → (∀ i, MemLp (p i) 2 volume) →
      (∀ i, HasWeakPartialDeriv i (p i) u univ) →
      (∀ j, MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x) 2 volume) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, ∑ j : Fin d, (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in V, f x * φ x) →
      ∃ H : Fin d → Fin d → E → ℝ,
        (∀ i k, MemLp (H i k) 2 (volume.restrict W)) ∧
        (∀ i k, HasWeakPartialDeriv k (H i k) (p i) W) ∧
        (∫ x in W, ∑ k : Fin d, ∑ i : Fin d, H i k x ^ 2) ≤
          C * ((∫ x in V, ∑ i : Fin d, p i x ^ 2) +
            (∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨η, hη, hηc, hηrange, hηone, hηV, N, hN, hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hWc hV hWV
  obtain ⟨R, hR, hRV⟩ := hηc.isCompact.exists_cthickening_subset_open hV hηV
  let c : Fin d → ℝ := fun k => 2 * nirenbergMasterYoungConstant B N hVc k / B.lam
  have hc (k : Fin d) : 0 ≤ c k :=
    div_nonneg (mul_nonneg (by norm_num)
      (nirenbergMasterYoungConstant_nonneg B hN hVc k)) B.hlam_pos.le
  refine ⟨(d : ℝ) * ∑ k : Fin d, c k,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun k _ => hc k), ?_⟩
  intro u f p hu hf hp hw hF heq
  let energy : ℝ := (∫ x in V, ∑ i : Fin d, p i x ^ 2) +
    (∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2
  have henergy : 0 ≤ energy := by
    dsimp [energy]
    positivity
  have hquot (k : Fin d) (h : ℝ) (hh : h ≠ 0) (hhR : |h| ≤ R) :
      (∫ x in W, ∑ i : Fin d, diffQuot k h (p i) x ^ 2) ≤ c k * energy := by
    have hbound := diffQuot_weakGradient_localL2_bound_quantitative B hV hu hf hp hw
      hF heq hη hηc hηrange hN hDη hV hVΩ hVc (Subset.rfl) hR
      (fun {h} hh => (Metric.cthickening_mono hh _).trans hRV)
      (fun x hx => hηone x (subset_closure hx)) hW.measurableSet k hh hhR
    rw [mul_comm (B.lam / 2)] at hbound
    have h' := (le_div_iff₀ (div_pos B.hlam_pos (by norm_num : (0 : ℝ) < 2))).mpr hbound
    calc
      _ ≤ nirenbergMasterYoungConstant B N hVc k * energy / (B.lam / 2) := h'
      _ = _ := by dsimp [c]; rw [div_div_eq_mul_div]; ring
  have hex (i k : Fin d) := exists_weakPartial_eLpNorm_le_of_integral_diffQuot_bound
    hW hWc hp hR hquot i k
  choose H hHm hHw hHnorm using hex
  have hbound (i k : Fin d) : (∫ x in W, H i k x ^ 2) ≤ c k * energy := by
    have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hHnorm i k)
    rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hn
    rw [← eLpNorm_toReal_sq_eq_integral (hHm i k),
      ← Real.sq_sqrt (mul_nonneg (hc k) henergy)]
    exact (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mpr hn
  refine ⟨H, hHm, hHw, ?_⟩
  rw [integral_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun i _ => (hHm i k).integrable_sq))]
  calc
    _ ≤ ∑ k : Fin d, ∑ _i : Fin d, c k * energy := by
      apply Finset.sum_le_sum
      intro k _
      rw [integral_finsetSum _ (fun i _ => (hHm i k).integrable_sq)]
      exact Finset.sum_le_sum fun i _ => hbound i k
    _ = _ := by simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, energy]





theorem suWeak_local_hessian_integral_le
    {Ω O V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hO : IsOpen O) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ} {p : Fin d → E → ℝ},
      MemLp u 2 (volume.restrict O) → MemLp f 2 (volume.restrict V) →
      (∀ i, MemLp (p i) 2 (volume.restrict O)) →
      (∀ i, HasWeakPartialDeriv i (p i) u O) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, ∑ j : Fin d, (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in V, f x * φ x) →
      ∃ H : Fin d → Fin d → E → ℝ,
        (∀ i k, MemLp (H i k) 2 (volume.restrict W)) ∧
        (∀ i k, HasWeakPartialDeriv k (H i k) (p i) W) ∧
        (∫ x in W, ∑ k : Fin d, ∑ i : Fin d, H i k x ^ 2) ≤
          C * ((∫ x in V, ∑ i : Fin d, p i x ^ 2) +
            (∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := suWeak_hessian_integral_le B hV hVc hVΩ hW hWc hWV
  obtain ⟨χ, hχ, hχc, _, hχone, hχO⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVc hO hVO
  refine ⟨C, hC, ?_⟩
  intro u f p hu hf hp hw heq
  let u₀ : E → ℝ := fun x => χ x * u x
  let p₀ : Fin d → E → ℝ := fun i x => χ x * p i x +
    fderiv ℝ χ x (EuclideanSpace.single i 1) * u x
  let f₀ : E → ℝ := V.indicator f
  have huK (K : Set E) (_ : IsCompact K) (hKO : K ⊆ O) :
      MemLp u 2 (volume.restrict K) :=
    hu.mono_measure (Measure.restrict_mono hKO le_rfl)
  have hpK (i : Fin d) (K : Set E) (_ : IsCompact K) (hKO : K ⊆ O) :
      MemLp (p i) 2 (volume.restrict K) :=
    (hp i).mono_measure (Measure.restrict_mono hKO le_rfl)
  have hu₀ : MemLp u₀ 2 volume :=
    Poincare.Analysis.Elliptic.memLp_mul_of_compact_memLp huK hχ.continuous hχc hχO
  have hp₀ (i : Fin d) : MemLp (p₀ i) 2 volume :=
    Poincare.Analysis.Elliptic.memLp_cutoff_weakPartial i huK (hpK i) hχ hχc hχO
  have hw₀ (i : Fin d) : HasWeakPartialDeriv i (p₀ i) u₀ univ :=
    Poincare.Analysis.Elliptic.hasWeakPartialDeriv_cutoff i huK (hpK i) (hw i)
      hχ hχc hχO
  have hp₀c (i : Fin d) : HasCompactSupport (p₀ i) :=
    hχc.mul_right.add (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_right
  have hf₀ : MemLp f₀ 2 volume :=
    (memLp_indicator_iff_restrict hV.measurableSet).mpr hf
  have hF (j : Fin d) : MemLp (fun x => ∑ i : Fin d, B.a x i j * p₀ i x) 2 volume :=
    memLp_finsetSum _ (fun i _ =>
      Poincare.Analysis.Elliptic.memLp_continuous_mul_of_hasCompactSupport
        (B.continuous_a i j) (hp₀ i) (hp₀c i))
  have hident := Poincare.Analysis.Elliptic.cutoff_eqOn_of_eq_one (u := u) (p := p) hV
    (fun x hx => hχone x (subset_closure hx))
  have huEq : EqOn u₀ u V := hident.1
  have hpEq (i : Fin d) : EqOn (p₀ i) (p i) V := hident.2 i
  have heq₀ (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφV : tsupport φ ⊆ V) :
      (∫ x in V, ∑ j : Fin d, (∑ i : Fin d, B.a x i j * p₀ i x) *
        fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in V, f₀ x * φ x := by
    calc
      _ = ∫ x in V, ∑ j : Fin d, (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1) := by
        apply setIntegral_congr_fun hV.measurableSet
        intro x hx
        simp only [hpEq _ hx]
      _ = ∫ x in V, f x * φ x := heq φ hφ hφc hφV
      _ = _ := by
        apply setIntegral_congr_fun hV.measurableSet
        intro x hx
        simp [f₀, hx]
  obtain ⟨H, hHm, hHw, hHb⟩ := hbound hu₀ hf₀ hp₀ hw₀ hF heq₀
  refine ⟨H, hHm, ?_, ?_⟩
  · intro i k φ hφ hφc hφW
    calc
      _ = ∫ x in W, p₀ i x * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
        apply setIntegral_congr_fun hW.measurableSet
        intro x hx
        simp only [hpEq i (hWV (subset_closure hx))]
      _ = _ := hHw i k φ hφ hφc hφW
  · have hpint : (∫ x in V, ∑ i : Fin d, p₀ i x ^ 2) =
        ∫ x in V, ∑ i : Fin d, p i x ^ 2 := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x hx
      simp only [hpEq _ hx]
    have huint : (∫ x in V, u₀ x ^ 2) = ∫ x in V, u x ^ 2 := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x hx
      simp only [huEq hx]
    have hfint : (∫ x in V, f₀ x ^ 2) = ∫ x in V, f x ^ 2 := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x hx
      simp [f₀, hx]
    rwa [hpint, huint, hfint] at hHb

end PoincareConjecture.M60

end
