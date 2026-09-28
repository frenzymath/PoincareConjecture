import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsDriftGlobal
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsTargetWeighted
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsForcingContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingCompactJets
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingExteriorJets
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingExteriorIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

theorem raw_intrinsic_gauge_forcing_weighted_jets_bounded
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ eta : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    (ht₀ : t₀ ∈ Icc 0 T) (heta : 0 ≤ eta) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T,
      ∀ x : EuclideanSpace ℝ (Fin 5), ∀ sigma, |sigma| ≤ eta →
      (1 + ‖x‖) *
      ‖iteratedFDeriv ℝ j (fun p : EuclideanSpace ℝ (Fin 5) × ℝ => smoothGaugeForcing
        (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t) r))
        (rawWarpingRadius P G hrotation t₀)
        (axisDivision (rawRadialVelocity P G hrotation t)) p.1 p.2) (x, sigma)‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin 5)
  let A := Icc (0 : ℝ) T
  let f (t : A) := rawWarpingRadius P G hrotation t.1
  let v (t : A) := rawRadialVelocity P G hrotation t.1
  let h (t : A) (r : ℝ) := Real.log (axisDivision (f t) r)
  let xi (t : A) := axisDivision (v t)
  let tbase : A := ⟨t₀, ht₀⟩
  have ht (t : A) : t.1 ∈ Ico 0 G.lifetime := ⟨t.2.1, t.2.2.trans_lt hTlt⟩
  have hf (t : A) : ContDiff ℝ ∞ (f t) := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hfo (t : A) : Function.Odd (f t) := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact intrinsicWarpingRadius_odd _ _ _
  have hfzero (t : A) : f t 0 = 0 := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t), intrinsicWarpingRadius_zero]
  have hdfzero (t : A) : deriv (f t) 0 = 1 := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact (intrinsicWarpingRadius_hasDerivAt_zero _ _ _).deriv
  have hpos (t : A) (r : ℝ) (hr : 0 < r) : 0 < f t r := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact intrinsicWarpingRadius_pos _ _ _ hr
  have hhe (t : A) : h t = intrinsicLogWarping (G.flow.metric t.1)
      (hrotation t.1 (ht t)) (G.complete P (ht t)) := by
    dsimp only [h, f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    rfl
  have hhs (t : A) : ContDiff ℝ ∞ (h t) := by
    rw [hhe]
    exact intrinsicLogWarping_contDiff _ _ _
  have hhp (t : A) : Function.Even (h t) := by
    rw [hhe]
    exact intrinsicLogWarping_even _ _ _
  have hhz (t : A) : h t 0 = 0 := by
    rw [hhe, intrinsicLogWarping_zero]
  have hvs (t : A) : ContDiff ℝ ∞ (v t) := by
    dsimp only [v]
    rw [rawRadialVelocity_eq P G hrotation (ht t)]
    exact intrinsicRadialVelocity_contDiff _ _ _
  have hvo (t : A) : Function.Odd (v t) := by
    dsimp only [v]
    rw [rawRadialVelocity_eq P G hrotation (ht t)]
    exact intrinsicRadialVelocity_odd _ _ _
  have hvis (t : A) : ContDiff ℝ ∞ (xi t) := axisDivision_contDiff (hvs t)
  have hvie (t : A) : Function.Even (xi t) := axisDivision_even_of_odd (hvs t) (hvo t)
  have hnear := smoothGaugeForcing_compact_jets (E := E) (eta := eta)
    hhs hhp hvis hvie (hf tbase) (hfo tbase)
    (raw_intrinsic_log_jet_continuous_subtype P G hrotation hT.le hTlt)
    (raw_intrinsic_xi_jet_continuous_subtype P G hrotation hT.le hTlt)
  let c (t : A) (r : ℝ) := radialGaugeDrift (f t) (v t) r / r
  let invf (t : A) (r : ℝ) := 1 / f t r
  let target (p : E × ℝ) := smoothTargetCoupling (f tbase) ‖Real.exp p.2 • p.1‖
  have hcs (t : A) : ContDiffOn ℝ ∞ (c t) (Ioi 0) := by
    have hd : ContDiffOn ℝ ∞ (radialGaugeDrift (f t) (v t)) (Ioi 0) :=
      (((contDiffOn_const.mul (contDiff_infty_iff_deriv.mp (hf t)).2.contDiffOn).div
        (hf t).contDiffOn (fun r hr => (hpos t r hr).ne')).sub
        (contDiffOn_const.div contDiffOn_id (fun _ hr => ne_of_gt hr))).sub (hvs t).contDiffOn
    exact hd.div contDiffOn_id (fun _ hr => ne_of_gt hr)
  have hcb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t r, 1 ≤ r →
      (1 + r) * |iteratedDeriv j (c t) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ := raw_intrinsic_drift_coefficient_weighted_jets
      P H G hrotation hT hTlt j
    exact ⟨C, hC, fun t r hr => hCb t.1 t.2 r hr⟩
  have his (t : A) : ContDiffOn ℝ ∞ (invf t) (Ioi 0) :=
    contDiffOn_const.div (hf t).contDiffOn (fun r hr => (hpos t r hr).ne')
  have hfb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t r, 1 ≤ r →
      |iteratedDeriv j (f t) r| ≤ C := by
    obtain ⟨C, hC, hCb⟩ :=
      raw_intrinsic_warping_jets_bounded_on_slab P H G hT hTlt hrotation j
    refine ⟨C, hC.le, ?_⟩
    intro t r hr
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact hCb t.1 t.2 r (zero_le_one.trans hr)
  obtain ⟨floor, hfloor, hfloorb⟩ := raw_intrinsic_warping_tail_floor
    P G hrotation hT.le hTlt
  have hib := positive_reciprocal_exterior_jets_bounded hfloor
    (fun t => (hf t).contDiffOn) hpos (fun t r hr => hfloorb t.1 t.2 r hr) hfb
  have htarget : ContDiff ℝ ∞ target :=
    (smoothTargetCoupling_contDiff_norm (hf tbase) (hfo tbase)).comp
      (contDiff_snd.exp.smul contDiff_fst)
  have htargetb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E × ℝ, |p.2| ≤ eta →
      (1 + ‖p.1‖) * ‖iteratedFDeriv ℝ j target p‖ ≤ C := by
    obtain ⟨C, hC, hCb⟩ := raw_intrinsic_dilated_target_weighted_jets
      P H G hrotation hT hTlt ht₀ heta 1 j
    simp only [pow_one] at hCb
    exact ⟨C, hC.le, fun p hp => hCb p.1 p.2 hp⟩
  have hfar := exterior_forcing_formula_jets hcs his hcb hib htarget htargetb
  have hmap (t : A) : mapRadius (h t) = f t := by
    rw [hhe]
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation (ht t)]
    exact funext (fun r => (intrinsicWarpingRadius_eq_exp _ _ _ r).symm)
  have hvelocity (t : A) : (fun r => r * xi t r) = v t := by
    funext r
    have hz : v t 0 = 0 := by
      dsimp only [v]
      rw [rawRadialVelocity_eq P G hrotation (ht t), intrinsicRadialVelocity_zero]
    simpa only [xi, hz, sub_zero] using mul_axisDivision (hvs t) r
  let U : Set (E × ℝ) := {p | p.1 ≠ 0}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage continuous_fst
  have heq (t : A) : EqOn (fun p : E × ℝ => smoothGaugeForcing (h t) (f tbase)
      (xi t) p.1 p.2) (fun p : E × ℝ => c t ‖p.1‖ + 2 / ‖p.1‖ ^ 2 -
        2 * target p * invf t ‖p.1‖ ^ 2) U := by
    intro p hp
    have hformula := smoothGaugeForcing_eq_exterior_formula (xi := xi t)
      (hhs t) (hhp t) (hhz t)
      (hf tbase) (hfo tbase) (hfzero tbase) (hdfzero tbase) hp p.2
    rw [hmap, hvelocity] at hformula
    exact hformula
  intro j
  obtain ⟨C, hC, hCb⟩ := hnear j
  obtain ⟨D, hD, hDb⟩ := hfar j
  refine ⟨2 * C + D, by positivity, ?_⟩
  intro t htime x sigma hsigma
  let a : A := ⟨t, htime⟩
  by_cases hx : ‖x‖ ≤ 1
  · have hw := mul_le_mul (show 1 + ‖x‖ ≤ 2 by linarith only [hx])
      (hCb a x sigma hx hsigma) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    exact hw.trans (le_add_of_nonneg_right hD)
  · have hrad : 1 ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    have hxU : (x, sigma) ∈ U := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hrad)
    have hjet := (heq a).iteratedFDerivWithin (𝕜 := ℝ) j hxU
    rw [iteratedFDerivWithin_of_isOpen _ hU hxU,
      iteratedFDerivWithin_of_isOpen _ hU hxU] at hjet
    change (1 + ‖x‖) *
      ‖iteratedFDeriv ℝ j (fun p : E × ℝ => smoothGaugeForcing (h a) (f tbase)
        (xi a) p.1 p.2) (x, sigma)‖ ≤ 2 * C + D
    rw [hjet]
    exact (hDb a x sigma hrad hsigma).trans (le_add_of_nonneg_left (by positivity))

theorem raw_intrinsic_gauge_forcing_jets_bounded
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ eta : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    (ht₀ : t₀ ∈ Icc 0 T) (heta : 0 ≤ eta) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T,
      ∀ x : EuclideanSpace ℝ (Fin 5), ∀ sigma, |sigma| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : EuclideanSpace ℝ (Fin 5) × ℝ => smoothGaugeForcing
        (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t) r))
        (rawWarpingRadius P G hrotation t₀)
        (axisDivision (rawRadialVelocity P G hrotation t)) p.1 p.2) (x, sigma)‖ ≤ C := by
  intro j
  obtain ⟨C, hC, hCb⟩ := raw_intrinsic_gauge_forcing_weighted_jets_bounded
    P H G hrotation hT hTlt ht₀ heta j
  refine ⟨C, hC, ?_⟩
  intro t ht x sigma hsigma
  have h := hCb t ht x sigma hsigma
  nlinarith only [h, mul_nonneg (norm_nonneg x)
    (norm_nonneg (iteratedFDeriv ℝ j (fun p : EuclideanSpace ℝ (Fin 5) × ℝ =>
      smoothGaugeForcing
        (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t) r))
        (rawWarpingRadius P G hrotation t₀)
        (axisDivision (rawRadialVelocity P G hrotation t)) p.1 p.2) (x, sigma)))]

end PoincareConjecture.M35.Uniqueness
