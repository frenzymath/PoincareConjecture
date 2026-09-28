import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsVelocityBound
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsTailFloor
import PoincareConjecture.Proofs.M35.RadialGauge.ScalarExteriorReciprocal
import PoincareConjecture.Proofs.M35.RadialGauge.ExteriorDriftJets











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness



theorem raw_intrinsic_drift_coefficient_weighted_jets
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ r ≥ 1,
      (1 + r) * |iteratedDeriv j (fun s =>
        RadialGauge.radialGaugeDrift (rawWarpingRadius P G hrotation t)
          (rawRadialVelocity P G hrotation t) s / s) r| ≤ C := by
  let A := Icc (0 : ℝ) T
  let f (t : A) := rawWarpingRadius P G hrotation t.1
  let v (t : A) := rawRadialVelocity P G hrotation t.1
  have ht (t : A) : t.1 ∈ Ico 0 G.lifetime := ⟨t.2.1, t.2.2.trans_lt hTlt⟩
  have hf (t : A) : ContDiff ℝ ∞ (f t) := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hv (t : A) : ContDiff ℝ ∞ (v t) := by
    dsimp only [v]
    rw [rawRadialVelocity_eq P G hrotation (ht t)]
    exact intrinsicRadialVelocity_contDiff _ _ _
  have hp (t : A) (r : ℝ) (hr : 0 < r) : 0 < f t r := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact intrinsicWarpingRadius_pos _ _ _ hr
  have hb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t r, 1 ≤ r →
      |iteratedDeriv j (f t) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_warping_jets_bounded_on_slab P H G hT hTlt hrotation j
    refine ⟨C, hC.le, ?_⟩
    intro t r hr
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact hCb t.1 t.2 r (zero_le_one.trans hr)
  have hV (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t r, 1 ≤ r →
      |iteratedDeriv j (v t) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_velocity_jets_bounded_on_slab P H G hrotation hT hTlt j
    exact ⟨C, hC.le, fun t r hr => hCb t.1 t.2 r (zero_le_one.trans hr)⟩
  obtain ⟨c, hc, hfloor⟩ := raw_intrinsic_warping_tail_floor P G hrotation hT.le hTlt
  have hI := RadialGauge.positive_reciprocal_exterior_jets_bounded hc
    (fun t => (hf t).contDiffOn) hp (fun t r hr => hfloor t.1 t.2 r hr) hb
  intro j
  obtain ⟨C, hC, hCb⟩ :=
    RadialGauge.radialGaugeDrift_div_radius_weighted_jets hf hv hp hb hI hV j
  exact ⟨C, hC, fun t ht => hCb ⟨t, ht⟩⟩

end PoincareConjecture.M35.Uniqueness
