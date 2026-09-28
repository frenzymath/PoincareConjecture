import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.SecondDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.L2
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.LocalEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.TestCalculus









noncomputable section

open Set MeasureTheory Function Filter Topology
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem partial_eqOn {U : Set E} (hU : IsOpen U) {u v : E → ℝ}
    (heq : EqOn u v U) (i : Fin d) : EqOn (partialDeriv i u) (partialDeriv i v) U := by
  intro x hx
  have hloc : u =ᶠ[𝓝 x] v := Filter.mem_of_superset (hU.mem_nhds hx) heq
  exact congrArg (fun A : E →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) hloc.fderiv_eq

private theorem localized_principal_equation
    {Ω V U : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hU : IsOpen U) (hUV : U ⊆ V) {u v f : E → ℝ}
    (huv : EqOn v u U)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, ∑ j : Fin d, (∑ i : Fin d, B.a x i j * partialDeriv i v x) *
        partialDeriv j φ x) = ∫ x in U, U.indicator f x * φ x := by
  intro φ hφ hφc hφU
  have hraw : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      (∫ x in V, ∑ i : Fin d, ∑ j : Fin d, B.a x i j * partialDeriv j u x *
        fderiv ℝ ψ x (EuclideanSpace.single i 1)) = ∫ x in V, f x * ψ x := by
    intro ψ hψ hψc hψV
    rw [← heq ψ hψ hψc hψV]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [SmoothEllipticBilinearForm.principalIntegrand, partialDeriv]
    rw [Finset.sum_comm]
    simp only [B.symm]
  have hloc := weakEquation_congr_restrict hUV (show EqOn B.a B.a U from fun _ _ => rfl)
    (fun i => partial_eqOn hU huv i) hraw φ hφ hφc hφU
  calc
    _ = ∫ x in U, f x * φ x := by simpa only [B.symm, partialDeriv] using hloc
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simp [hx]

theorem principal_equation_restrict
    {Ω V U : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hU : IsOpen U) (hUV : U ⊆ V) {u f : E → ℝ}
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, B.principalIntegrand u φ x) = ∫ x in U, f x * φ x := by
  intro φ hφ hφc hφU
  have h := localized_principal_equation B hU hUV (fun _ _ => rfl) heq φ hφ hφc hφU
  calc
    _ = ∫ x in U, ∑ j : Fin d, (∑ i : Fin d, B.a x i j * partialDeriv i u x) *
        partialDeriv j φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [SmoothEllipticBilinearForm.principalIntegrand, partialDeriv,
        Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∫ x in U, U.indicator f x * φ x := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simp [hx]



theorem exists_hessian_integral_le_of_weakEquation
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
      (∫ x in W, ∑ k : Fin d, ∑ i : Fin d, (partialDeriv k (partialDeriv i u) x) ^ 2) ≤
        C * ((∫ x in V, ∑ i : Fin d, (partialDeriv i u x) ^ 2) +
          (∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨η, hη, hηc, hηrange, hηone, hηV, N, hN, hDη⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff_with_fderiv_bound hWc hV hWV
  obtain ⟨R, hR, hRV⟩ := hηc.isCompact.exists_cthickening_subset_open hV hηV
  obtain ⟨χ, hχ, hχc, _, hχone, _⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVc isOpen_univ (subset_univ _)
  let c : Fin d → ℝ := fun k => 2 * nirenbergMasterYoungConstant B N hVc k / B.lam
  have hc (k : Fin d) : 0 ≤ c k :=
    div_nonneg (mul_nonneg (by norm_num)
      (nirenbergMasterYoungConstant_nonneg B hN hVc k)) B.hlam_pos.le
  refine ⟨(d : ℝ) * ∑ k : Fin d, c k,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun k _ => hc k)), ?_⟩
  intro u f hu hf heq
  let u₀ : E → ℝ := fun x => χ x * u x
  let p₀ : Fin d → E → ℝ := fun i => partialDeriv i u₀
  let f₀ : E → ℝ := V.indicator f
  have hu₀ : ContDiff ℝ ∞ u₀ := hχ.mul hu
  have hu₀c : HasCompactSupport u₀ := hχc.mul_right
  have hu₀m : MemLp u₀ 2 volume := hu₀.continuous.memLp_of_hasCompactSupport hu₀c
  have hp₀ (i : Fin d) : ContDiff ℝ ∞ (p₀ i) := contDiff_partial hu₀ i
  have hp₀c (i : Fin d) : HasCompactSupport (p₀ i) := hasCompactSupport_partial hu₀c i
  have hp₀m (i : Fin d) : MemLp (p₀ i) 2 volume :=
    (hp₀ i).continuous.memLp_of_hasCompactSupport (hp₀c i)
  have hf₀ : MemLp f₀ 2 volume :=
    (memLp_indicator_iff_restrict hV.measurableSet).mpr hf
  have hF (j : Fin d) : MemLp (fun x => ∑ i : Fin d, B.a x i j * p₀ i x) 2 volume :=
    memLp_finsetSum _ (fun i _ => memLp_continuous_mul_of_hasCompactSupport
      (B.continuous_a i j) (hp₀m i) (hp₀c i))
  have huEq : EqOn u₀ u V := fun x hx => by
    dsimp [u₀]
    rw [hχone x (subset_closure hx), one_mul]
  have hpEq (i : Fin d) : EqOn (p₀ i) (partialDeriv i u) V := partial_eqOn hV huEq i
  have hppEq (i k : Fin d) : EqOn (partialDeriv k (p₀ i))
      (partialDeriv k (partialDeriv i u)) V := partial_eqOn hV (hpEq i) k
  have hpint : (∫ x in V, ∑ i : Fin d, (p₀ i x) ^ 2) =
      ∫ x in V, ∑ i : Fin d, (partialDeriv i u x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp only [hpEq _ hx]
  have huint : (∫ x in V, u₀ x ^ 2) = ∫ x in V, u x ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    rw [huEq hx]
  have hfint : (∫ x in V, f₀ x ^ 2) = ∫ x in V, f x ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp [f₀, hx]
  let energy : ℝ := (∫ x in V, ∑ i : Fin d, (partialDeriv i u x) ^ 2) +
    (∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2
  have hbound (i k : Fin d) :
      (∫ x in W, (partialDeriv k (partialDeriv i u) x) ^ 2) ≤ c k * energy := by
    have h := classicalPartial_integral_sq_le_nirenberg B hV hu₀m hf₀ hp₀m
      (fun i => (hp₀ i).of_le (by simp))
      (fun i => HasWeakPartialDeriv.of_contDiff isOpen_univ (hu₀.of_le (by simp)))
      hF (localized_principal_equation B hV (Subset.rfl) huEq heq)
      hη hηc hηrange hN hDη hV hVΩ hVc (Subset.rfl) hR
      (fun {h} hh => (Metric.cthickening_mono hh _).trans hRV)
      (fun x hx => hηone x (subset_closure hx)) hW hWc i k
    rw [hpint, huint, hfint] at h
    change (∫ x in W, (partialDeriv k (p₀ i) x) ^ 2) ≤ c k * energy at h
    convert h using 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hW.measurableSet] with x hx
    rw [hppEq i k (hWV (subset_closure hx))]
  have hint (i k : Fin d) : Integrable
      (fun x => (partialDeriv k (partialDeriv i u) x) ^ 2) (volume.restrict W) :=
    ((continuous_memLp_on_compact (contDiff_partial (contDiff_partial hu i) k).continuous
      hWc).mono_measure (Measure.restrict_mono subset_closure le_rfl)).integrable_sq
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => hint i k))]
  calc
    _ ≤ ∑ k : Fin d, ∑ _i : Fin d, c k * energy := by
      apply Finset.sum_le_sum
      intro k _
      rw [integral_finsetSum _ (fun i _ => hint i k)]
      exact Finset.sum_le_sum (fun i _ => hbound i k)
    _ = _ := by simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, energy]

end Poincare.Analysis.Elliptic.InteriorEstimates
