import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsVelocity
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingContinuity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

theorem raw_intrinsic_gauge_forcing_continuous
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T : ℝ} (hT : 0 ≤ T) (hTlt : T < G.lifetime) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Continuous (fun p : (Icc (0 : ℝ) T × E) × ℝ => smoothGaugeForcing
      (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation p.1.1.1) r))
      (rawWarpingRadius P G hrotation t₀)
      (axisDivision (rawRadialVelocity P G hrotation p.1.1.1)) p.1.2 p.2) := by
  have hh (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞
      (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t.1) r)) := by
    rw [rawWarpingRadius_eq P G hrotation ⟨t.2.1, t.2.2.trans_lt hTlt⟩]
    exact intrinsicLogWarping_contDiff _ _ _
  have hf : ContDiff ℝ ∞ (rawWarpingRadius P G hrotation t₀) := by
    rw [rawWarpingRadius_eq P G hrotation ⟨ht₀.1, ht₀.2.trans_lt hTlt⟩]
    exact intrinsicWarpingRadius_contDiff _ _ _
  apply smoothGaugeForcing_parametric_continuous
    (xi := fun t : Icc (0 : ℝ) T => axisDivision (rawRadialVelocity P G hrotation t.1)) hh hf
    (raw_intrinsic_log_jet_continuous_subtype P G hrotation hT hTlt)
  simpa only [iteratedDeriv_zero] using
    raw_intrinsic_xi_jet_continuous_subtype P G hrotation hT hTlt 0

end PoincareConjecture.M35.Uniqueness
