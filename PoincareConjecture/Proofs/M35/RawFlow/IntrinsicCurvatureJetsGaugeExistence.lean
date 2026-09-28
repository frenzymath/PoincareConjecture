import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsGaugeCoefficients
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsForcingEnd
import PoincareConjecture.Proofs.M35.RadialGauge.GaugeEquation
import PoincareConjecture.Proofs.M35.RadialGauge.SmoothGaugeEnd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

local notation "V" => EuclideanSpace ℝ (Fin 5)
local notation "Cov" => V →L[ℝ] ℝ

noncomputable local instance m35RawGaugeExistenceLocal1 :
    NormedAddCommGroup Cov := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35RawGaugeExistenceLocal2 :
    NormedSpace ℝ Cov := ContinuousLinearMap.toNormedSpace
noncomputable local instance m35RawGaugeExistenceLocal3 :
    NormedAddCommGroup (V →L[ℝ] Cov) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35RawGaugeExistenceLocal4 :
    NormedSpace ℝ (V →L[ℝ] Cov) := ContinuousLinearMap.toNormedSpace

theorem exists_raw_intrinsic_smooth_gauge
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht₀ : t₀ ∈ Ico 0 T) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ T - t₀ ∧ ∃ u : ℝ → V → ℝ,
      u 0 = 0 ∧
      Continuous (fun p : Icc 0 delta × V => u p.1.1 p.2) ∧
      Continuous (fun p : Icc 0 delta × V => fderiv ℝ (u p.1.1) p.2) ∧
      (∀ j : ℕ, ∃ D : ℝ, ∀ t ∈ Icc 0 delta, ∀ x,
        ‖iteratedFDeriv ℝ j (u t) x‖ ≤ D) ∧
      (∀ t ∈ Icc 0 delta, ContDiff ℝ ∞ (u t) ∧
        (∀ (Q : V ≃ₗᵢ[ℝ] V) x, u t (Q x) = u t x) ∧
        (∀ x, (1 + ‖x‖) * ‖u t x‖ ≤ 1 / 8 ∧
          (1 + ‖x‖) * ‖fderiv ℝ (u t) x‖ ≤ 1 / 8) ∧
        (∀ x, u t x = gaugeDuhamel
          (fun s => rawIntrinsicGaugeDrift P G hrotation (t₀ + s))
          (fun s => rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + s)) u t x) ∧
        ∀ k x,
          (1 + ‖x‖) * ‖gaugePicard
            (fun s => rawIntrinsicGaugeDrift P G hrotation (t₀ + s))
            (fun s => rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + s)) k t x - u t x‖ ≤
              (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k ∧
          (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard
            (fun s => rawIntrinsicGaugeDrift P G hrotation (t₀ + s))
            (fun s => rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + s)) k t) x -
            fderiv ℝ (u t) x‖ ≤ (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ k) ∧
      (∃ H J : ℝ, 0 ≤ H ∧ 0 ≤ J ∧ ∀ t ∈ Icc 0 delta, ∀ x,
        (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ H ∧
        (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u t))) x‖ ≤ J) ∧
      (∀ e > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 delta, ∀ x, R ≤ ‖x‖ →
        (1 + ‖x‖) * ‖fderiv ℝ (u t) x‖ < e ∧
        (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (u t)) x‖ < e) ∧
      ∀ t ∈ Ioo 0 delta, ∀ x, HasDerivAt (fun s => u s x)
        (euclideanLaplacian (u t) x + gaugeSource
          (rawIntrinsicGaugeDrift P G hrotation (t₀ + t))
          (rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + t)) (u t) x) t := by
  let b := fun s => rawIntrinsicGaugeDrift P G hrotation (t₀ + s)
  let F := fun s => rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + s)
  let eta : ℝ := 1 / 8
  have heta : 0 < eta := by norm_num [eta]
  have ht₀cc : t₀ ∈ Icc 0 T := ⟨ht₀.1, ht₀.2.le⟩
  obtain ⟨B, L, C, hB, hL, hC, hb, hzero, hlip⟩ :=
    raw_intrinsic_gauge_coefficient_constants P G hrotation H hT hTlt ht₀cc heta.le
  have hdrift := raw_intrinsic_gauge_drift_controls P H G hrotation hT hTlt (E := V)
  have hforcing := raw_intrinsic_gauge_forcing_jets_bounded
    P H G hrotation hT hTlt ht₀cc heta.le
  obtain ⟨delta, hd, hdT, hball, hcontract, hhigh⟩ :=
    exists_common_smooth_gauge_time (n := 4) heta
      (show 0 ≤ B * eta + eta ^ 2 + L * eta + C by positivity)
      (show 0 ≤ L + B + 2 * eta by positivity)
      (show 0 ≤ B + 2 * (4 + 1 : ℕ) * eta by positivity)
      (sub_pos.mpr ht₀.2)
  have hshift (s : ℝ) (hs : s ∈ Icc 0 delta) : t₀ + s ∈ Icc 0 T := by
    constructor
    · exact add_nonneg ht₀.1 hs.1
    · linarith only [hs.2, hdT]
  let shift : Icc (0 : ℝ) delta → Icc (0 : ℝ) T :=
    fun s => ⟨t₀ + s.1, hshift s.1 s.2⟩
  have hcshift : Continuous shift :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  have hbc : Continuous (fun p : Icc 0 delta × V => b p.1.1 p.2) :=
    hdrift.1.comp (f := fun p : Icc 0 delta × V => (shift p.1, p.2))
      ((hcshift.comp continuous_fst).prodMk continuous_snd)
  have hFc : Continuous (fun p : (Icc 0 delta × V) × ℝ => F p.1.1.1 p.1.2 p.2) :=
    (raw_intrinsic_gauge_forcing_continuous P G hrotation hT.le hTlt ht₀cc (E := V)).comp
      (f := fun p : (Icc 0 delta × V) × ℝ => ((shift p.1.1, p.1.2), p.2))
      (((hcshift.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hbs (s : ℝ) (hs : s ∈ Icc 0 delta) : ContDiff ℝ ∞ (b s) :=
    hdrift.2.1 (t₀ + s) (hshift s hs)
  have hFs (s : ℝ) (hs : s ∈ Icc 0 delta) :
      ContDiff ℝ ∞ (fun p : V × ℝ => F s p.1 p.2) :=
    rawIntrinsicGaugeForcing_contDiff P G hrotation
      ⟨ht₀.1, ht₀.2.trans hTlt⟩
      ⟨(hshift s hs).1, (hshift s hs).2.trans_lt hTlt⟩
  have hbb (j : ℕ) : ∃ D : ℝ, ∀ s ∈ Icc 0 delta, ∀ x,
      ‖iteratedFDeriv ℝ j (b s) x‖ ≤ D := by
    obtain ⟨D, _hD, hDb⟩ := hdrift.2.2 j
    exact ⟨D, fun s hs => hDb (t₀ + s) (hshift s hs)⟩
  have hFb (j : ℕ) : ∃ D : ℝ, ∀ s ∈ Icc 0 delta, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => F s p.1 p.2) (x, z)‖ ≤ D := by
    obtain ⟨D, _hD, hDb⟩ := hforcing j
    exact ⟨D, fun s hs => hDb (t₀ + s) (hshift s hs)⟩
  obtain ⟨u, _hmu, hcu, hcdu, hu0, _hout, hub, hsource, hu⟩ :=
    exists_gauge_smooth_mild_solution (n := 4) hd.le heta.le hB hL hC
      hbc.stronglyMeasurable hFc.measurable hbs hFs hbb hFb
      (fun s hs => hb (t₀ + s) (hshift s hs))
      (fun s hs => hzero (t₀ + s) (hshift s hs))
      (fun s hs => hlip (t₀ + s) (hshift s hs)) hball
      (hcontract.trans (by norm_num)) hhigh
  have hequiv (Q : V ≃ₗᵢ[ℝ] V) (s : ℝ) (x : V) : b s (Q x) = Q (b s x) :=
    rawIntrinsicGaugeDrift_equivariant P G hrotation Q (t₀ + s) x
  have hinvariant (Q : V ≃ₗᵢ[ℝ] V) (s : ℝ) (x : V) (z : ℝ) :
      F s (Q x) z = F s x z :=
    rawIntrinsicGaugeForcing_invariant P G hrotation Q t₀ (t₀ + s) x z
  have hradial (s : ℝ) (hs : s ∈ Icc 0 delta) (Q : V ≃ₗᵢ[ℝ] V) (x : V) :
      u s (Q x) = u s x := by
    have hlim := (hu s hs).2.2.2.1
    apply tendsto_nhds_unique (hlim.tendsto_at (Q x))
    simpa only [gaugePicard_invariant Q (hequiv Q) (hinvariant Q)]
      using hlim.tendsto_at x
  have hFw (j : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ Icc 0 delta, ∀ x z, |z| ≤ eta →
      (1 + ‖x‖) * ‖iteratedFDeriv ℝ j (fun p : V × ℝ => F s p.1 p.2) (x, z)‖ ≤ D := by
    obtain ⟨D, hD, hDb⟩ := raw_intrinsic_gauge_forcing_weighted_jets_bounded
      P H G hrotation hT hTlt ht₀cc heta.le j
    exact ⟨D, hD, fun s hs => hDb (t₀ + s) (hshift s hs)⟩
  have hFend : ∀ e > 0, ∃ R : ℝ, ∀ s ∈ Icc 0 delta, ∀ x z, R ≤ ‖x‖ → |z| ≤ eta →
      (1 + ‖x‖) * ‖forcingSpaceDeriv (F s) x z‖ < e := by
    intro e he
    obtain ⟨R, hR⟩ := raw_intrinsic_gauge_forcing_space_vanishes
      P H G hrotation hT hTlt ht₀cc e he (eta := eta)
    exact ⟨R, fun s hs => hR (t₀ + s) (hshift s hs)⟩
  have hend := smooth_gauge_limit_weighted_end hd.le heta.le hB hL hC
    hbc.stronglyMeasurable hFc.measurable hbs hFs hbb hFw
    (fun s hs => hb (t₀ + s) (hshift s hs))
    (fun s hs => hzero (t₀ + s) (hshift s hs))
    (fun s hs => hlip (t₀ + s) (hshift s hs)) hball hcontract hhigh
    (fun s hs => (hu s hs).1.differentiable (by simp))
    (fun s hs x => (hu s hs).2.2.2.1.tendsto_at x)
    (fun s hs => (hu s hs).2.2.2.2.1)
    (fun k s hs x => ((hu s hs).2.2.2.2.2 k x).2) hFend
  refine ⟨delta, hd, hdT, u, hu0, hcu, hcdu, hub, ?_, hend.1, hend.2, ?_⟩
  · intro s hs
    refine ⟨(hu s hs).1, hradial s hs, (hu s hs).2.2.1, (hu s hs).2.1, ?_⟩
    intro k x
    simpa only [eta, show (2 : ℝ) * (1 / 8) = 1 / 4 by norm_num] using
      (hu s hs).2.2.2.2.2 k x
  · intro t ht x
    exact gauge_smooth_mild_solves_heat hbc hFc hcu hcdu hbs hFs
      (fun s hs => (hu s hs).1) hsource (fun s hs => (hu s hs).2.1) ht x

end PoincareConjecture.M35.Uniqueness
