import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.HigherOrder
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.LowerOrder
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.H1Profile








noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)


def ellipticPowerProfile (a : E → Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → E → ℝ) (V : Set E) (n : ℕ) (u : E → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (n + 1), derivativeProfile 2 V 0 ((secondOrderOperator a b)^[j] u)

theorem ellipticPowerProfile_mono_order
    (a : E → Matrix (Fin d) (Fin d) ℝ) (b : Fin d → E → ℝ)
    (V : Set E) {r s : ℕ} (hrs : r ≤ s) (u : E → ℝ) :
    ellipticPowerProfile a b V r u ≤ ellipticPowerProfile a b V s u := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hrs 1)) (fun _ _ _ => zero_le)

theorem ellipticPowerProfile_operator_le
    (a : E → Matrix (Fin d) (Fin d) ℝ) (b : Fin d → E → ℝ)
    (V : Set E) (r : ℕ) (u : E → ℝ) :
    ellipticPowerProfile a b V r (secondOrderOperator a b u) ≤
      ellipticPowerProfile a b V (r + 1) u := by
  unfold ellipticPowerProfile
  rw [Finset.sum_range_succ' (n := r + 1)]
  simp only [Function.iterate_succ_apply]
  exact le_self_add

theorem derivativeProfile_zero_le_ellipticPowerProfile
    (a : E → Matrix (Fin d) (Fin d) ℝ) (b : Fin d → E → ℝ)
    (V : Set E) (n : ℕ) (u : E → ℝ) :
    derivativeProfile 2 V 0 u ≤ ellipticPowerProfile a b V n u := by
  have h := ellipticPowerProfile_mono_order a b V (Nat.zero_le n) u
  simpa [ellipticPowerProfile] using h

theorem contDiff_iterate_secondOrderOperator
    {a : E → Matrix (Fin d) (Fin d) ℝ} {b : Fin d → E → ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ContDiff ℝ ∞ ((secondOrderOperator a b)^[n] u) := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_secondOrderOperator ha hb ih

theorem ellipticPowerProfile_ne_top
    {a : E → Matrix (Fin d) (Fin d) ℝ} {b : Fin d → E → ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) {V : Set E} (hVc : IsCompact (closure V))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    ellipticPowerProfile a b V n u ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  rw [derivativeProfile_zero]
  exact ((continuous_memLp_on_compact
    (contDiff_iterate_secondOrderOperator ha hb hu j).continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)).eLpNorm_ne_top



theorem exists_derivativeProfile_le_ellipticPowerProfile [NeZero d]
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (b : Fin d → E → ℝ) (hb : ∀ i, ContDiff ℝ ∞ (b i)) (n : ℕ)
    {V W : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ ∞ u →
      derivativeProfile 2 W n u ≤ ENNReal.ofReal C * ellipticPowerProfile B.a b V n u := by
  induction n using Nat.strong_induction_on generalizing V W with
  | h n ih =>
      cases n with
      | zero =>
          refine ⟨1, zero_le_one, ?_⟩
          intro u hu
          simpa [ellipticPowerProfile] using
            derivativeProfile_mono_set (subset_closure.trans hWV) 2 0 u
      | succ n =>
          cases n with
          | zero =>
              obtain ⟨C, hC, hbound⟩ := exists_derivativeProfile_one_le_with_drift B
                hV hVc (subset_closure.trans hVΩ) hW hWc hWV (driftCorrection B.a b)
                (contDiff_driftCorrection B.smooth_a hb)
              refine ⟨C, hC, ?_⟩
              intro u hu
              have hLu := contDiff_secondOrderOperator B.smooth_a hb hu
              have hmem := (continuous_memLp_on_compact hLu.neg.continuous hVc).mono_measure
                (Measure.restrict_mono subset_closure le_rfl)
              have heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
                  (∫ x in V, B.principalIntegrand u φ x) =
                    ∫ x in V, (-secondOrderOperator B.a b u x +
                      ∑ i, driftCorrection B.a b i x * partialDeriv i u x) * φ x := by
                intro φ hφ hφc hφV
                rw [principal_equation_of_smooth B hV hu φ hφ hφc hφV]
                apply integral_congr_ae
                exact Eventually.of_forall fun x => by
                  change principalSource B.a u x * φ x =
                    (-secondOrderOperator B.a b u x +
                      ∑ i, driftCorrection B.a b i x * partialDeriv i u x) * φ x
                  exact congrArg (fun z : ℝ => z * φ x)
                    (principalSource_eq_secondOrderOperator b B.smooth_a hu x)
              have h := hbound hu hmem heq
              simpa [ellipticPowerProfile, Finset.sum_range_succ, derivativeProfile_neg] using h
          | succ r =>
              obtain ⟨U, hU, hWU, hUV⟩ :=
                hWc.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hWV)
              have hUc : IsCompact (closure U) :=
                hVc.of_isClosed_subset isClosed_closure (hUV.trans subset_closure)
              have hUΩ : closure U ⊆ Ω := hUV.trans (subset_closure.trans hVΩ)
              obtain ⟨H, hH, hprincipal⟩ :=
                exists_derivativeProfile_add_two_le_source B r hU hUc hUΩ hW hWc hWU
              obtain ⟨D, hD, hsource⟩ :=
                exists_principalSource_profile_le hU hUc B.a b B.smooth_a hb r
              obtain ⟨A, hA, hoperator⟩ := ih r (by omega) hV hVc hVΩ hU hUc hUV
              obtain ⟨F, hF, hlower⟩ := ih (r + 1) (by omega) hV hVc hVΩ hU hUc hUV
              refine ⟨H * (1 + D * (A + F)), by positivity, ?_⟩
              intro u hu
              let P := ellipticPowerProfile B.a b V (r + 2) u
              have hzero : derivativeProfile 2 U 0 u ≤ P :=
                (derivativeProfile_mono_set (subset_closure.trans hUV) 2 0 u).trans
                  (derivativeProfile_zero_le_ellipticPowerProfile B.a b V (r + 2) u)
              have hop : derivativeProfile 2 U r (secondOrderOperator B.a b u) ≤
                  ENNReal.ofReal A * P := by
                apply (hoperator (contDiff_secondOrderOperator B.smooth_a hb hu)).trans
                apply mul_le_mul_of_nonneg_left _ zero_le
                exact (ellipticPowerProfile_operator_le B.a b V r u).trans
                  (ellipticPowerProfile_mono_order B.a b V (by omega) u)
              have huLower : derivativeProfile 2 U (r + 1) u ≤ ENNReal.ofReal F * P := by
                apply (hlower hu).trans
                apply mul_le_mul_of_nonneg_left _ zero_le
                exact ellipticPowerProfile_mono_order B.a b V (by omega) u
              have hs : derivativeProfile 2 U r (principalSource B.a u) ≤
                  ENNReal.ofReal (D * (A + F)) * P := by
                apply (hsource hu).trans
                calc
                  _ ≤ ENNReal.ofReal D * (ENNReal.ofReal A * P + ENNReal.ofReal F * P) :=
                    mul_le_mul_of_nonneg_left (add_le_add hop huLower) zero_le
                  _ = _ := by
                    rw [ENNReal.ofReal_mul hD, ENNReal.ofReal_add hA hF]
                    ring
              have h := hprincipal hu (contDiff_principalSource B.smooth_a hu)
                (weakEquation_principalSource hU B.smooth_a hu)
              apply h.trans
              calc
                _ ≤ ENNReal.ofReal H * (P + ENNReal.ofReal (D * (A + F)) * P) :=
                  mul_le_mul_of_nonneg_left (add_le_add hzero hs) zero_le
                _ = _ := by
                  rw [ENNReal.ofReal_mul hH,
                    ENNReal.ofReal_add zero_le_one (mul_nonneg hD (add_nonneg hA hF)),
                    ENNReal.ofReal_one]
                  ring

end Poincare.Analysis.Elliptic.InteriorEstimates
