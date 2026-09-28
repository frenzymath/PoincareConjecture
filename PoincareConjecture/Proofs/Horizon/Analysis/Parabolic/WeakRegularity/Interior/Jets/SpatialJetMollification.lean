




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.SpatialJetAlgebra
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakConvolution
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.KernelBuffer
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.MollifiedL2Energy











open Set MeasureTheory Filter Metric
open Poincare.Analysis.Convolution
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

theorem HasSpatialL2Jet.congr_ae
    {n k : ℕ} {U : Set (Spacetime n)} {u v : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (huv : u =ᵐ[volume.restrict U] v) :
    HasSpatialL2Jet U k v := by
  cases k with
  | zero => exact MemLp.ae_eq huv hu
  | succ k =>
    obtain ⟨hum, g, hg, hweak⟩ := hu
    refine ⟨MemLp.ae_eq huv hum, g, hg, ?_⟩
    intro i φ hφ hφc hφU
    rw [hweak i φ hφ hφc hφU]
    congr 1
    exact integral_congr_ae (huv.mono fun y hy =>
      congrArg (fun a => spatialDeriv i φ y * a) hy)


def iteratedSpatialDeriv {n : ℕ} :
    (k : ℕ) → (Fin k → Fin n) → (Spacetime n → ℝ) → Spacetime n → ℝ
  | 0, _, u => u
  | k + 1, p, u => iteratedSpatialDeriv k (Fin.tail p) (spatialDeriv (p 0) u)

private theorem iteratedSpatialDeriv_congr
    {n k : ℕ} {V : Set (Spacetime n)} {u w : Spacetime n → ℝ}
    (hV : IsOpen V) (huw : EqOn u w V) :
    ∀ p : Fin k → Fin n, EqOn (iteratedSpatialDeriv k p u) (iteratedSpatialDeriv k p w) V := by
  induction k generalizing u w with
  | zero => intro p; exact huw
  | succ k ih =>
    intro p
    apply ih
    intro y hy
    exact congrArg (fun A : Spacetime n →L[ℝ] ℝ => A (spatialDirection (p 0)))
      (huw.eventuallyEq_of_mem (hV.mem_nhds hy)).fderiv_eq

theorem HasSpatialL2Jet.exists_mollified_iterated_representatives
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (hU : IsOpen U) :
    ∃ G : (Fin k → Fin n) → Spacetime n → ℝ,
      (∀ p, MemLp (G p) 2 (volume.restrict U)) ∧
      ∀ (η : Spacetime n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∀ (V : Set (Spacetime n)), IsOpen V →
          (∀ x ∈ V, tsupport (translatedKernel η x) ⊆ U) →
          ∀ p : Fin k → Fin n,
            EqOn (iteratedSpatialDeriv k p (lebesgueConvolution η u))
              (lebesgueConvolution η (U.indicator (G p))) V := by
  induction k generalizing u with
  | zero =>
    refine ⟨fun _ => u, fun _ => hu, ?_⟩
    intro η hη hηc V hV hs p x hx
    change (∫ y, η (x-y) * u y) = ∫ y, η (x-y) * U.indicator u y
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ U
    · rw [indicator_of_mem hy]
    · have hzero : η (x-y) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := translatedKernel η x)
          (fun h => hy (hs x hx h))
      rw [hzero, zero_mul, zero_mul]
  | succ k ih =>
    obtain ⟨hum, g, hg, hweak⟩ := hu
    have hrep (i : Fin n) := ih (hg i)
    choose G hGm hGe using hrep
    refine ⟨fun p => G (p 0) (Fin.tail p), fun p => hGm (p 0) (Fin.tail p), ?_⟩
    intro η hη hηc V hV hs p
    have hfirst : EqOn (spatialDeriv (p 0) (lebesgueConvolution η u))
        (lebesgueConvolution η (g (p 0))) V := by
      intro x hx
      exact fderiv_lebesgueConvolution_eq_weakDerivative hU
        (locallyIntegrableOn_of_locallyIntegrable_restrict (hum.locallyIntegrable (by norm_num)))
        (hg (p 0)).locallyIntegrableOn (hweak (p 0)) hη hηc (hs x hx)
    exact (iteratedSpatialDeriv_congr hV hfirst (Fin.tail p)).trans
      (hGe (p 0) η hη hηc V hV hs (Fin.tail p))

theorem HasSpatialL2Jet.exists_uniform_mollified_spatial_energy
    {n k : ℕ} {U : Set (Spacetime n)} {u : Spacetime n → ℝ}
    (hu : HasSpatialL2Jet U k u) (hU : IsOpen U)
    {z : Spacetime n} (hz : z ∈ U)
    {ρ : Spacetime n → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ U ∧
      ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
        (∫ y in ball z s, ∑ p : Fin k → Fin n,
          (iteratedSpatialDeriv k p (mollifiedValue u ρ r) y) ^ 2) ≤ B := by
  classical
  obtain ⟨G, hGm, hGe⟩ := hu.exists_mollified_iterated_representatives hU
  let G₀ (p : Fin k → Fin n) := U.indicator (G p)
  have hG₀ (p : Fin k → Fin n) : MemLp (G₀ p) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).mpr (hGm p)
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let s := R / 2
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsU : closedBall z s ⊆ U := by
    intro y hy
    apply hRU
    exact (mem_closedBall.mp hy).trans_lt (by dsimp only [s]; linarith)
  obtain ⟨ε, hε, hsupport⟩ := exists_uniform_translated_rescaledKernel_support_subset
    (isCompact_closedBall z s) hU hsU hρc
  let A : ℝ := ∑ p : Fin k → Fin n, (∫ y, ‖ρ y‖) ^ 2 * (∫ y, G₀ p y ^ 2)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun p _ =>
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun y => sq_nonneg _)))
  refine ⟨s, hs, hsU, ε, A + 1, hε, by positivity, ?_⟩
  intro r hr hrε
  have hscale : ContDiff ℝ ∞ (rescaledKernel ρ r) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have hderiv (p : Fin k → Fin n) {y : Spacetime n} (hy : y ∈ ball z s) :
      iteratedSpatialDeriv k p (mollifiedValue u ρ r) y = mollifiedValue (G₀ p) ρ r y :=
    hGe (rescaledKernel ρ r) hscale hcompact (ball z s) isOpen_ball
      (fun x hx => hsupport r hr hrε x (ball_subset_closedBall hx)) p hy
  have hsq (p : Fin k → Fin n) : Integrable (fun y => mollifiedValue (G₀ p) ρ r y ^ 2) :=
    (memLp_lebesgueConvolution (hG₀ p) hscale.continuous hcompact).integrable_sq
  calc
    (∫ y in ball z s, ∑ p : Fin k → Fin n,
        (iteratedSpatialDeriv k p (mollifiedValue u ρ r) y) ^ 2) =
        ∫ y in ball z s, ∑ p : Fin k → Fin n, mollifiedValue (G₀ p) ρ r y ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      simp_rw [hderiv _ hy]
    _ ≤ ∫ y, ∑ p : Fin k → Fin n, mollifiedValue (G₀ p) ρ r y ^ 2 :=
      setIntegral_le_integral (integrable_finsetSum _ (fun p _ => hsq p))
        (Eventually.of_forall (fun y => Finset.sum_nonneg (fun p _ => sq_nonneg _)))
    _ = ∑ p : Fin k → Fin n, ∫ y, mollifiedValue (G₀ p) ρ r y ^ 2 :=
      integral_finsetSum _ (fun p _ => hsq p)
    _ ≤ A := Finset.sum_le_sum (fun p _ =>
      integral_mollifiedValue_sq_le (hG₀ p) hρ.continuous hρc hr)
    _ ≤ A + 1 := by linarith

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
