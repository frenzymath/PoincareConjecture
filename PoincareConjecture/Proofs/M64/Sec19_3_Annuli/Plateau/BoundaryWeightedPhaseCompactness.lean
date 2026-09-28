import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakLocalizedCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseL2
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Density
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak EuclideanTranslationNative

local notation "S" => interior m64AnnulusDomain

theorem m64WeakPhase_weighted_l2_isCompact
    (u : ℕ → LoopPlane → ℝ) (hw : ∀ j, MemW1pWitness 2 (u j) S)
    {A C : ℝ} (hA : ∀ j, (∫ p in S, (u j p) ^ 2) ≤ A)
    (hC : ∀ j i, (∫ p in S, ((hw j).weakGrad p i) ^ 2) ≤ C) :
    ∃ rho : LoopPlane → ℝ, ContDiff ℝ ∞ rho ∧
      (∀ p ∈ S, 0 < rho p) ∧ (∀ p, rho p ∈ Icc (0 : ℝ) 1) ∧
      (∀ p ∉ S, rho p = 0) ∧
      ∃ hF : ∀ j, MemLp (fun p => rho p * u j p) 2 volume,
        IsCompact (closure (range (fun j => (hF j).toLp (fun p => rho p * u j p)))) := by
  obtain ⟨rho, hsupp, hrho, hrange⟩ :=
    isOpen_interior.exists_contDiff_support_eq (n := (⊤ : ℕ∞)) (s := S)
  have h01 (p : LoopPlane) : rho p ∈ Icc (0 : ℝ) 1 := hrange (mem_range_self p)
  have hout (p : LoopPlane) (hp : p ∉ S) : rho p = 0 := by
    apply Function.notMem_support.mp
    rwa [hsupp]
  have hin (p : LoopPlane) (hp : p ∈ S) : 0 < rho p :=
    lt_of_le_of_ne (h01 p).1 (Ne.symm (by
      change p ∈ Function.support rho
      rwa [hsupp]))
  have hS : MeasurableSet S := isOpen_interior.measurableSet
  have hU (j : ℕ) : MemLp ((S).indicator (u j)) 2 volume :=
    (memLp_indicator_iff_restrict hS).mpr (hw j).memLp
  have hF (j : ℕ) : MemLp (fun p => rho p * u j p) 2 volume := by
    have heq : (fun p => rho p * u j p) = fun p => rho p * (S).indicator (u j) p := by
      funext p
      by_cases hp : p ∈ S
      · rw [indicator_of_mem hp]
      · rw [hout p hp, zero_mul, zero_mul]
    rw [heq]
    apply (hU j).of_le_mul (hrho.continuous.aestronglyMeasurable.mul (hU j).aestronglyMeasurable)
      (c := 1)
    filter_upwards with p
    simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (h01 p).1]
    exact mul_le_mul_of_nonneg_right (h01 p).2 (norm_nonneg _)
  let F (j : ℕ) := (hF j).toLp (fun p => rho p * u j p)
  have hA0 : 0 ≤ A := (integral_nonneg (fun p => sq_nonneg (u 0 p))).trans (hA 0)
  have hTB : TotallyBounded (range F) := by
    apply Metric.totallyBounded_iff.mpr
    intro epsilon hepsilon
    let delta := epsilon / (2 * (Real.sqrt A + 1))
    have hdelta : 0 < delta := div_pos hepsilon (by positivity)
    let K := m64AnnulusDomain ∩ {p : LoopPlane | delta ≤ rho p}
    have hK : IsCompact K := m64AnnulusDomain_isCompact.inter_right
      (isClosed_le continuous_const hrho.continuous)
    have hKS : K ⊆ S := by
      intro p hp
      by_contra hn
      have hh : delta ≤ rho p := hp.2
      rw [hout p hn] at hh
      exact (not_le_of_gt hdelta) hh
    obtain ⟨radius, psi, -, -, hpsi, hc, hpsi01, hone, hsupport⟩ :=
      Poincare.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
        hK isOpen_interior hKS
    let theta := fun p => psi p * rho p
    have htheta : ContDiff ℝ (⊤ : ℕ∞) theta := hpsi.mul hrho
    obtain ⟨hV, hcompact⟩ := m64WeakSobolev_localized_l2_isCompact isOpen_interior u hw
      hA hC theta htheta hc.mul_right (tsupport_mul_subset_left.trans hsupport)
    let V (j : ℕ) := (hV j).toLp (fun p => theta p * u j p)
    have herror (j : ℕ) : dist (F j) (V j) < epsilon / 2 := by
      rw [dist_eq_norm]
      apply (sq_lt_sq₀ (norm_nonneg _) (half_pos hepsilon).le).mp
      let w := fun p => rho p * u j p - theta p * u j p
      have hwL : MemLp w 2 volume := (hF j).sub (hV j)
      have hpoint (p : LoopPlane) : w p ^ 2 ≤ delta ^ 2 * ((S).indicator (u j) p) ^ 2 := by
        by_cases hp : p ∈ S
        · rw [indicator_of_mem hp]
          by_cases hpK : p ∈ K
          · have honep := hone p (Metric.self_subset_cthickening K hpK)
            simp only [w, theta, honep, one_mul, sub_self, zero_pow (by decide : 2 ≠ 0)]
            positivity
          · have hr : rho p < delta := by
              apply lt_of_not_ge
              intro hh
              exact hpK ⟨interior_subset hp, hh⟩
            have hps := hpsi01 (mem_range_self p)
            have hcoef0 : 0 ≤ rho p * (1 - psi p) :=
              mul_nonneg (h01 p).1 (sub_nonneg.mpr hps.2)
            have hcoef : rho p * (1 - psi p) ≤ delta := by nlinarith [hps.1, (h01 p).1]
            have hsquare := (sq_le_sq₀ hcoef0 hdelta.le).mpr hcoef
            have hmul := mul_le_mul_of_nonneg_right hsquare (sq_nonneg (u j p))
            dsimp only [w, theta]
            nlinarith
        · simp only [w, theta, hout p hp, mul_zero, zero_mul, sub_self,
            indicator_of_notMem hp, zero_pow (by decide : 2 ≠ 0), le_refl]
      have hUbound : (∫ p, ((S).indicator (u j) p) ^ 2) ≤ A := by
        have heq : (fun p => ((S).indicator (u j) p) ^ 2) =
            (S).indicator (fun p => (u j p) ^ 2) := by
          funext p
          by_cases hp : p ∈ S <;> simp [hp]
        rw [heq, integral_indicator hS]
        exact hA j
      have hsmall : delta ^ 2 * A < (epsilon / 2) ^ 2 := by
        have hsqrt := Real.sq_sqrt hA0
        have hsqrt0 := Real.sqrt_nonneg A
        have hden : Real.sqrt A + 1 ≠ 0 := by positivity
        dsimp only [delta]
        field_simp
        nlinarith [sq_pos_of_pos hepsilon]
      calc
        ‖F j - V j‖ ^ 2 = ∫ p, w p ^ 2 := by
          dsimp only [F, V]
          rw [← MemLp.toLp_sub, scalar_toLp_norm_sq]
          rfl
        _ ≤ ∫ p, delta ^ 2 * ((S).indicator (u j) p) ^ 2 :=
          integral_mono hwL.integrable_sq ((hU j).integrable_sq.const_mul _) hpoint
        _ ≤ delta ^ 2 * A := by rw [integral_const_mul]; gcongr
        _ < _ := hsmall
    obtain ⟨centers, hcenters, hcover⟩ := Metric.totallyBounded_iff.mp hcompact.totallyBounded
      (epsilon / 2) (half_pos hepsilon)
    refine ⟨centers, hcenters, ?_⟩
    rintro _ ⟨j, rfl⟩
    obtain ⟨v, hv⟩ := mem_iUnion.mp (hcover (subset_closure (mem_range_self j)))
    obtain ⟨hvcenters, hv⟩ := mem_iUnion.mp hv
    apply mem_iUnion.mpr
    refine ⟨v, mem_iUnion.mpr ⟨hvcenters, ?_⟩⟩
    rw [Metric.mem_ball] at hv ⊢
    exact (dist_triangle (F j) (V j) v).trans_lt (by linarith [herror j])
  exact ⟨rho, hrho, hin, h01, hout, hF, hTB.closure.isCompact_of_isClosed isClosed_closure⟩

end PoincareConjecture
