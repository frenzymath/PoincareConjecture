import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsGaugeExistence
import PoincareConjecture.Proofs.M35.RadialGauge.GaugeJointC1
import PoincareConjecture.Proofs.M35.RadialGauge.GaugeJetJointC1











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge

local notation "V" => EuclideanSpace ℝ (Fin 5)



theorem raw_intrinsic_gauge_spatial_time_jets
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ delta : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) (ht₀ : t₀ ∈ Ico 0 T)
    (hd : 0 ≤ delta) (hdT : delta ≤ T - t₀) {u : ℝ → V → ℝ}
    (hcu : Continuous (fun p : Icc 0 delta × V => u p.1.1 p.2))
    (hcdu : Continuous (fun p : Icc 0 delta × V => fderiv ℝ (u p.1.1) p.2))
    (hus : ∀ t ∈ Icc 0 delta, ContDiff ℝ ∞ (u t))
    (hub : ∀ j : ℕ, ∃ C : ℝ, ∀ t ∈ Icc 0 delta, ∀ x,
      ‖iteratedFDeriv ℝ j (u t) x‖ ≤ C)
    (hball : ∀ t ∈ Icc 0 delta, ∀ x, (1 + ‖x‖) * ‖u t x‖ ≤ 1 / 8)
    (hmild : ∀ t ∈ Icc 0 delta, ∀ x, u t x = gaugeDuhamel
      (fun s => rawIntrinsicGaugeDrift P G hrotation (t₀ + s))
      (fun s => rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + s)) u t x) :
    (∀ j : ℕ, Continuous
      (fun p : Icc 0 delta × V => iteratedFDeriv ℝ j (u p.1.1) p.2)) ∧
    (∀ (j : ℕ) (t : ℝ), t ∈ Ioo 0 delta → ∀ x,
      HasDerivAt (fun s => iteratedFDeriv ℝ j (u s) x)
        (iteratedFDeriv ℝ j (fun y => euclideanLaplacian (u t) y + gaugeSource
          (rawIntrinsicGaugeDrift P G hrotation (t₀ + t))
          (rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + t)) (u t) y) x) t) ∧
    ContDiffOn ℝ 1 (Function.uncurry u) (Ioo 0 delta ×ˢ univ) ∧
    (∀ j : ℕ, ContDiffOn ℝ 1
      (fun p : ℝ × V => iteratedFDeriv ℝ j (u p.1) p.2) (Ioo 0 delta ×ˢ univ)) := by
  let b := fun s => rawIntrinsicGaugeDrift P G hrotation (t₀ + s)
  let F := fun s => rawIntrinsicGaugeForcing P G hrotation t₀ (t₀ + s)
  have hshift (s : ℝ) (hs : s ∈ Icc 0 delta) : t₀ + s ∈ Icc 0 T := by
    constructor
    · exact add_nonneg ht₀.1 hs.1
    · linarith only [hs.2, hdT]
  let shift : Icc (0 : ℝ) delta → Icc (0 : ℝ) T :=
    fun s => ⟨t₀ + s.1, hshift s.1 s.2⟩
  have hcshift : Continuous shift :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  have hdrift := raw_intrinsic_gauge_drift_controls P H G hrotation hT hTlt (E := V)
  have ht₀cc : t₀ ∈ Icc 0 T := ⟨ht₀.1, ht₀.2.le⟩
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
  let : Nonempty (Icc (0 : ℝ) delta) := ⟨⟨0, le_rfl, hd⟩⟩
  have hsource := gaugeSource_uniform_bounded_derivatives
    (b := fun s : Icc 0 delta => b s.1) (G := fun s : Icc 0 delta => F s.1)
    (u := fun s : Icc 0 delta => u s.1)
    (fun s => hbs s.1 s.2) (fun s => hFs s.1 s.2) (fun s => hus s.1 s.2)
    (eta := (1 / 8 : ℝ))
    (fun s x => by
      have h := hball s.1 s.2 x
      rw [Real.norm_eq_abs] at h
      nlinarith only [h, mul_nonneg (norm_nonneg x) (abs_nonneg (u s.1 x))])
    (fun j => by
      obtain ⟨C, _hC, hC⟩ := hdrift.2.2 j
      exact ⟨C, fun s => hC (t₀ + s.1) (hshift s.1 s.2)⟩)
    (fun j => by
      obtain ⟨C, hC⟩ := hub j
      exact ⟨C, fun s => hC s.1 s.2⟩)
    (fun j => by
      obtain ⟨C, _hC, hC⟩ := raw_intrinsic_gauge_forcing_jets_bounded
        P H G hrotation hT hTlt ht₀cc (by norm_num : (0 : ℝ) ≤ 1 / 8) j
      exact ⟨C, fun s => hC (t₀ + s.1) (hshift s.1 s.2)⟩)
  have hsource' : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 delta, ∀ x,
      ‖iteratedFDeriv ℝ j (gaugeSource (b s) (F s) (u s)) x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hsource j
    exact ⟨C, fun s hs => hC ⟨s, hs⟩⟩
  have hj := gauge_smooth_mild_spatial_time_jets hbc hFc hcu hcdu hbs hFs hus hub
    hsource' hmild
  exact ⟨hj.1, hj.2,
    gauge_smooth_mild_joint_c1 hbc hFc hcu hcdu hbs hFs hus hub hsource' hmild,
    gauge_smooth_mild_jets_joint_c1 hbc hFc hcu hcdu hbs hFs hus hub hsource' hmild⟩

end PoincareConjecture.M35.Uniqueness
