import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture



theorem m64NonnegativeIntegral_subsequence
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    (f : ℕ → X → ℝ) (hf : ∀ j, Integrable (f j) mu)
    (hpos : ∀ j x, 0 ≤ f j x)
    (hlim : Tendsto (fun j => ∫ x, f j x ∂mu) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ x ∂mu, Tendsto (fun j => f (k j) x) atTop (𝓝 0) := by
  let F : ℕ → Lp ℝ 1 mu := fun j => (hf j).toL1 (f j)
  have hnorm (j : ℕ) : ‖F j‖ = ∫ x, f j x ∂mu := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [(hf j).coeFn_toL1] with x hx
    change (F j) x = f j x at hx
    rw [hx, Real.norm_eq_abs, abs_of_nonneg (hpos j x)]
  have hF : Tendsto F atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (by
    simpa only [hnorm] using hlim)
  obtain ⟨k, hk, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂mu, ∀ j, (F (k j)) x = f (k j) x :=
    ae_all_iff.mpr fun j => (hf (k j)).coeFn_toL1
  refine ⟨k, hk, ?_⟩
  filter_upwards [hae, hrep, Lp.coeFn_zero ℝ 1 mu] with x hx hxr hz
  simpa only [hxr, hz, Pi.zero_apply] using hx



theorem m64Annulus_strong_slice_subsequence
    {E : Type*} [NormedAddCommGroup E] {l : ℕ}
    (f : ℕ → Fin l → LoopPlane → E) (u : Fin l → LoopPlane → E)
    (hi : ∀ j i, IntegrableOn (fun p => ‖f j i p - u i p‖ ^ 2)
      (interior m64AnnulusDomain) volume)
    (hlim : ∀ i, Tendsto (fun j => ∫ p in interior m64AnnulusDomain,
      ‖f j i p - u i p‖ ^ 2) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ∀ i,
        Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
          ‖f (k j) i (annulusPoint x s) - u i (annulusPoint x s)‖ ^ 2) atTop (𝓝 0) := by
  let q := fun j i s => ∫ x in Icc (0 : ℝ) curvePeriod,
    ‖f j i (annulusPoint x s) - u i (annulusPoint x s)‖ ^ 2
  have hq (j : ℕ) (i : Fin l) : IntegrableOn (q j i) (Icc (0 : ℝ) 1) volume :=
    (m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable (hi j i)).integral_prod_right
  have hpos (j : ℕ) (i : Fin l) (s : ℝ) : 0 ≤ q j i s :=
    integral_nonneg fun x => sq_nonneg _
  have hqint (j : ℕ) (i : Fin l) : (∫ s in Icc (0 : ℝ) 1, q j i s) =
      ∫ p in interior m64AnnulusDomain, ‖f j i p - u i p‖ ^ 2 :=
    (m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _ (hi j i)).symm
  let Q := fun j s => ∑ i : Fin l, q j i s
  have hQ (j : ℕ) : IntegrableOn (Q j) (Icc (0 : ℝ) 1) volume :=
    integrable_finsetSum Finset.univ fun i _ => hq j i
  have hQpos (j : ℕ) (s : ℝ) : 0 ≤ Q j s :=
    Finset.sum_nonneg fun i _ => hpos j i s
  have hQlim : Tendsto (fun j => ∫ s in Icc (0 : ℝ) 1, Q j s) atTop (𝓝 0) := by
    have heq (j : ℕ) : (∫ s in Icc (0 : ℝ) 1, Q j s) =
        ∑ i : Fin l, ∫ p in interior m64AnnulusDomain, ‖f j i p - u i p‖ ^ 2 := by
      rw [integral_finsetSum Finset.univ (fun i _ => hq j i)]
      simp only [hqint]
    simpa only [heq, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  obtain ⟨k, hk, hslice⟩ := m64NonnegativeIntegral_subsequence Q hQ hQpos hQlim
  refine ⟨k, hk, ?_⟩
  filter_upwards [hslice] with s hs
  intro i
  exact squeeze_zero (fun j => hpos (k j) i s)
    (fun j => Finset.single_le_sum (fun b _ => hpos (k j) b s) (Finset.mem_univ i)) hs

end PoincareConjecture
