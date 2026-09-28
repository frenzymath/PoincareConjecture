import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.H2Profile
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Commutator

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem principal_equation_of_weakEquation {Ω V : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {u f : E → ℝ}
    (heq : WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u)) f) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x := by
  intro φ hφ hφc hφV
  have h := heq φ hφ hφc hφV
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SmoothEllipticBilinearForm.principalIntegrand, matrixFlux,
    partialDeriv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [B.symm]

omit [NeZero d] in
private theorem smooth_differentiatedSource
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    {u f : E → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f) (k : Fin d) :
    ContDiff ℝ ∞ (differentiatedSource A (fun j => partialDeriv j u)
      (fun i j => partialDeriv i (partialDeriv j u)) (partialDeriv k f) k) := by
  apply ContDiff.add (contDiff_partial hf k)
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_partial (hA i j) k).mul (contDiff_partial (contDiff_partial hu j) i)).add
    ((contDiff_partial (contDiff_partial (hA i j) k) i).mul (contDiff_partial hu j))

omit [NeZero d] in
private theorem weakEquation_partial {V : Set E} (hV : IsOpen V)
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    {u f : E → ℝ} (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
    (heq : WeakEquation V (matrixFlux A (fun j => partialDeriv j u)) f) (k : Fin d) :
    WeakEquation V (matrixFlux A (fun j => partialDeriv j (partialDeriv k u)))
      (differentiatedSource A (fun j => partialDeriv j u)
        (fun i j => partialDeriv i (partialDeriv j u)) (partialDeriv k f) k) := by
  have hlocal {v : E → ℝ} (hv : Continuous v) : LocallyIntegrable v (volume.restrict V) :=
    hv.locallyIntegrable.mono_measure Measure.restrict_le_self
  have hdiff := differentiated_equation hV k hA
    (fun j => hlocal (contDiff_partial hu j).continuous)
    (fun i j => hlocal (contDiff_partial (contDiff_partial hu j) i).continuous)
    (hlocal (contDiff_partial hf k).continuous)
    (fun i j => HasWeakPartialDeriv.of_contDiff (i := i) hV
      ((contDiff_partial hu j).of_le (by simp)))
    (HasWeakPartialDeriv.of_contDiff (i := k) hV (hf.of_le (by simp))) heq
  apply hdiff.congr_flux
  intro i
  exact Eventually.of_forall fun x => by
    unfold matrixFlux
    apply Finset.sum_congr rfl
    intro j hj
    change A x i j * partialDeriv k (partialDeriv j u) x =
      A x i j * partialDeriv j (partialDeriv k u) x
    exact congrArg (fun v : E → ℝ => A x i j * v x) (partial_comm hu k j)

theorem exists_derivativeProfile_add_two_le_source
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω) (k : ℕ)
    {V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u → ContDiff ℝ ∞ f →
      WeakEquation V (matrixFlux B.a (fun j => partialDeriv j u)) f →
      derivativeProfile 2 W (k + 2) u ≤ ENNReal.ofReal C *
        (derivativeProfile 2 V 0 u + derivativeProfile 2 V k f) := by
  induction k generalizing V W with
  | zero =>
      obtain ⟨C, hC, hbound⟩ := exists_derivativeProfile_two_le_source B hV hVc hVΩ hW hWc hWV
      refine ⟨C, hC, ?_⟩
      intro u f hu hf heq
      exact hbound hu ((continuous_memLp_on_compact hf.continuous hVc).mono_measure
        (Measure.restrict_mono subset_closure le_rfl)) (principal_equation_of_weakEquation B heq)
  | succ k ih =>
      obtain ⟨U, hU, hWU, hUV⟩ := hWc.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hWV)
      have hUc : IsCompact (closure U) :=
        hVc.of_isClosed_subset isClosed_closure (hUV.trans subset_closure)
      have hUΩ : closure U ⊆ Ω := hUV.trans (subset_closure.trans hVΩ)
      obtain ⟨A, hA, hprior⟩ := ih hV hVc hVΩ hU hUc hUV
      obtain ⟨H, hH, hpartial⟩ := ih hU hUc hUΩ hW hWc hWU
      choose D hD hcomm using fun i => differentiatedSource_profile_le hU hUc B.a B.smooth_a k i
      let coeff : Fin d → ℝ := fun i => H * (A + D i * (A + 1))
      have hcoeff (i : Fin d) : 0 ≤ coeff i :=
        mul_nonneg hH (add_nonneg hA (mul_nonneg (hD i) (add_nonneg hA zero_le_one)))
      let C : ℝ := 1 + ∑ i, coeff i
      refine ⟨C, add_nonneg zero_le_one (Finset.sum_nonneg (fun i hi => hcoeff i)), ?_⟩
      intro u f hu hf heq
      let T := derivativeProfile 2 V 0 u + derivativeProfile 2 V (k + 1) f
      let source : Fin d → E → ℝ := fun i =>
        differentiatedSource B.a (fun j => partialDeriv j u)
          (fun a b => partialDeriv a (partialDeriv b u)) (partialDeriv i f) i
      have heqU := heq.restrict (subset_closure.trans hUV)
      have huU : derivativeProfile 2 U (k + 2) u ≤ ENNReal.ofReal A * T := by
        apply (hprior hu hf heq).trans
        dsimp [T]
        gcongr
        exact derivativeProfile_mono_order (Nat.le_succ k) f
      have hfU : derivativeProfile 2 U (k + 1) f ≤ T :=
        (derivativeProfile_mono_set (subset_closure.trans hUV) 2 (k + 1) f).trans le_add_self
      have hpart0 (i : Fin d) : derivativeProfile 2 U 0 (partialDeriv i u) ≤
          ENNReal.ofReal A * T :=
        ((derivativeProfile_partial_le 0 i hu).trans
          (derivativeProfile_mono_order (by omega : 1 ≤ k + 2) u)).trans huU
      have hsource (i : Fin d) : derivativeProfile 2 U k (source i) ≤
          ENNReal.ofReal (D i * (A + 1)) * T := by
        apply (hcomm i hu hf).trans
        calc
          ENNReal.ofReal (D i) *
              (derivativeProfile 2 U (k + 2) u + derivativeProfile 2 U (k + 1) f) ≤
              ENNReal.ofReal (D i) * (ENNReal.ofReal A * T + T) := by gcongr
          _ = ENNReal.ofReal (D i * (A + 1)) * T := by
            rw [ENNReal.ofReal_mul (hD i), ENNReal.ofReal_add hA zero_le_one,
              ENNReal.ofReal_one]
            ring
      have hpart (i : Fin d) : derivativeProfile 2 W (k + 2) (partialDeriv i u) ≤
          ENNReal.ofReal (coeff i) * T := by
        have h := hpartial (contDiff_partial hu i)
          (smooth_differentiatedSource B.a B.smooth_a hu hf i)
          (weakEquation_partial hU B.a B.smooth_a hu hf heqU i)
        apply h.trans
        calc
          ENNReal.ofReal H *
              (derivativeProfile 2 U 0 (partialDeriv i u) + derivativeProfile 2 U k (source i)) ≤
              ENNReal.ofReal H *
                (ENNReal.ofReal A * T + ENNReal.ofReal (D i * (A + 1)) * T) := by
                  exact mul_le_mul_of_nonneg_left (add_le_add (hpart0 i) (hsource i)) zero_le
          _ = ENNReal.ofReal (coeff i) * T := by
            dsimp [coeff]
            rw [ENNReal.ofReal_mul hH,
              ENNReal.ofReal_add hA (mul_nonneg (hD i) (by positivity))]
            ring
      have hu0 : derivativeProfile 2 W 0 u ≤ T :=
        (derivativeProfile_mono_set (subset_closure.trans hWV) 2 0 u).trans le_self_add
      have hreconstruct := derivativeProfile_succ_le_sum_partial
        (Ω := W) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (k + 2) hu
      have horder : k + 1 + 2 = k + 2 + 1 := by omega
      rw [horder]
      apply hreconstruct.trans
      apply (add_le_add hu0 (Finset.sum_le_sum (fun i hi => hpart i))).trans_eq
      dsimp [C]
      rw [ENNReal.ofReal_add zero_le_one (Finset.sum_nonneg (fun i hi => hcoeff i)),
        ENNReal.ofReal_one, ENNReal.ofReal_sum_of_nonneg (fun i hi => hcoeff i),
        add_mul, one_mul, Finset.sum_mul]

end Poincare.Analysis.Elliptic.InteriorEstimates
