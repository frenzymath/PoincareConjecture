import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsForcing
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

local notation "V" => EuclideanSpace ℝ (Fin 5)

noncomputable def rawIntrinsicGaugeDrift (t : ℝ) : V → V :=
  smoothGaugeDrift
    (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t) r))
    (axisDivision (rawRadialVelocity P G hrotation t))

noncomputable def rawIntrinsicGaugeForcing (t₀ t : ℝ) : V → ℝ → ℝ :=
  smoothGaugeForcing
    (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t) r))
    (rawWarpingRadius P G hrotation t₀)
    (axisDivision (rawRadialVelocity P G hrotation t))

theorem rawIntrinsicGaugeForcing_contDiff {t₀ t : ℝ}
    (ht₀ : t₀ ∈ Ico 0 G.lifetime) (ht : t ∈ Ico 0 G.lifetime) :
    ContDiff ℝ ∞ (fun p : V × ℝ => rawIntrinsicGaugeForcing P G hrotation t₀ t p.1 p.2) := by
  unfold rawIntrinsicGaugeForcing
  rw [rawWarpingRadius_eq P G hrotation ht,
    rawWarpingRadius_eq P G hrotation ht₀, rawRadialVelocity_eq P G hrotation ht]
  exact smoothGaugeForcing_contDiff
    (intrinsicLogWarping_contDiff _ _ _) (intrinsicLogWarping_even _ _ _)
    (intrinsicWarpingRadius_contDiff _ _ _) (intrinsicWarpingRadius_odd _ _ _)
    (axisDivision_contDiff (intrinsicRadialVelocity_contDiff _ _ _))
    (axisDivision_even_of_odd (intrinsicRadialVelocity_contDiff _ _ _)
      (intrinsicRadialVelocity_odd _ _ _))

theorem raw_intrinsic_gauge_coefficient_constants
    (H : StandardCapEstimate g₀) {T t₀ eta : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (ht₀ : t₀ ∈ Icc 0 T) (heta : 0 ≤ eta) :
    ∃ B L C : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ 0 ≤ C ∧
      (∀ t ∈ Icc 0 T, ∀ x, ‖rawIntrinsicGaugeDrift P G hrotation t x‖ ≤ B) ∧
      (∀ t ∈ Icc 0 T, ∀ x,
        (1 + ‖x‖) * |rawIntrinsicGaugeForcing P G hrotation t₀ t x 0| ≤ C) ∧
      ∀ t ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
        |rawIntrinsicGaugeForcing P G hrotation t₀ t x a -
          rawIntrinsicGaugeForcing P G hrotation t₀ t x c| ≤ L * |a - c| := by
  obtain ⟨B, hB, hBb⟩ :=
    (raw_intrinsic_gauge_drift_controls P H G hrotation hT hTlt (E := V)).2.2 0
  obtain ⟨C, hC, hCb⟩ := raw_intrinsic_gauge_forcing_weighted_jets_bounded
    P H G hrotation hT hTlt ht₀ heta 0
  obtain ⟨L, hL, hLb⟩ := raw_intrinsic_gauge_forcing_jets_bounded
    P H G hrotation hT hTlt ht₀ heta 1
  simp only [norm_iteratedFDeriv_zero] at hBb hCb
  simp only [norm_iteratedFDeriv_one] at hLb
  refine ⟨B, L, C, hB, hL, hC, hBb, ?_, ?_⟩
  · intro t ht x
    simpa only [rawIntrinsicGaugeForcing, Real.norm_eq_abs]
      using hCb t ht x 0 (by simpa using heta)
  · intro t ht x a c ha hc
    let S : Set (V × ℝ) := univ ×ˢ Icc (-eta) eta
    have hS : Convex ℝ S := convex_univ.prod (convex_Icc (-eta) eta)
    have hs := rawIntrinsicGaugeForcing_contDiff P G hrotation
      ⟨ht₀.1, ht₀.2.trans_lt hTlt⟩ ⟨ht.1, ht.2.trans_lt hTlt⟩
    have h := hS.norm_image_sub_le_of_norm_fderiv_le
      (fun p _ => hs.differentiable (by simp) p)
      (fun p hp => hLb t ht p.1 p.2 (abs_le.mpr hp.2))
      (show (x, c) ∈ S from ⟨mem_univ _, abs_le.mp hc⟩)
      (show (x, a) ∈ S from ⟨mem_univ _, abs_le.mp ha⟩)
    simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      Real.norm_eq_abs, max_eq_right (abs_nonneg (a - c))] using h

theorem rawIntrinsicGaugeDrift_equivariant (Q : V ≃ₗᵢ[ℝ] V) (t : ℝ) (x : V) :
    rawIntrinsicGaugeDrift P G hrotation t (Q x) =
      Q (rawIntrinsicGaugeDrift P G hrotation t x) :=
  smoothGaugeDrift_equivariant _ _ Q x

theorem rawIntrinsicGaugeForcing_invariant (Q : V ≃ₗᵢ[ℝ] V)
    (t₀ t : ℝ) (x : V) (sigma : ℝ) :
    rawIntrinsicGaugeForcing P G hrotation t₀ t (Q x) sigma =
      rawIntrinsicGaugeForcing P G hrotation t₀ t x sigma :=
  smoothGaugeForcing_invariant _ _ _ Q x sigma

end PoincareConjecture.M35.Uniqueness
