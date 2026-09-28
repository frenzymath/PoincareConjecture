import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsDrift
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsVelocity
import PoincareConjecture.Proofs.M35.RadialGauge.RadialFamilyBounds
import PoincareConjecture.Proofs.M35.RadialGauge.SmoothGaugeIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

theorem raw_intrinsic_gauge_drift_controls
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    Continuous (fun p : Icc (0 : ℝ) T × E => smoothGaugeDrift
      (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation p.1.1) r))
      (axisDivision (rawRadialVelocity P G hrotation p.1.1)) p.2) ∧
    (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (smoothGaugeDrift
      (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t) r))
      (axisDivision (rawRadialVelocity P G hrotation t)) : E → E)) ∧
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ x : E,
      ‖iteratedFDeriv ℝ j (smoothGaugeDrift
        (fun r => Real.log (axisDivision (rawWarpingRadius P G hrotation t) r))
        (axisDivision (rawRadialVelocity P G hrotation t)) : E → E) x‖ ≤ C := by
  let A := Icc (0 : ℝ) T
  let f (t : A) := rawWarpingRadius P G hrotation t.1
  let v (t : A) := rawRadialVelocity P G hrotation t.1
  let h (t : A) (r : ℝ) := Real.log (axisDivision (f t) r)
  let xi (t : A) := axisDivision (v t)
  let c (t : A) (r : ℝ) := 2 * axisDivision (deriv (h t)) r - xi t r
  have ht (t : A) : t.1 ∈ Ico 0 G.lifetime := ⟨t.2.1, t.2.2.trans_lt hTlt⟩
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
  have hds (t : A) : ContDiff ℝ ∞ (axisDivision (deriv (h t))) :=
    axisDivision_contDiff (contDiff_infty_iff_deriv.mp (hhs t)).2
  have hcs (t : A) : ContDiff ℝ ∞ (c t) := (contDiff_const.mul (hds t)).sub (hvis t)
  have hce (t : A) : Function.Even (c t) := by
    intro r
    simp only [c, axisDivision_deriv_even (hhs t) (hhp t) r, hvie t r]
  have hcc (j : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv j (c p.1) p.2) := by
    have hd := axisDivision_jet_continuous
      (fun t => (contDiff_infty_iff_deriv.mp (hhs t)).2) j
      (by simpa only [iteratedDeriv_succ'] using
        raw_intrinsic_log_jet_continuous_subtype P G hrotation hT.le hTlt (j + 2))
    have htwo : Continuous (fun p : A × ℝ =>
        iteratedDeriv j (fun r => 2 * axisDivision (deriv (h p.1)) r) p.2) := by
      simpa only [iteratedDeriv_const_mul_field, Function.comp_def] using
        continuous_mul.comp ((continuous_const (y := (2 : ℝ))).prodMk hd)
    exact scalar_jet_continuous_sub j (fun t => contDiff_const.mul (hds t)) hvis htwo
      (raw_intrinsic_xi_jet_continuous_subtype P G hrotation hT.le hTlt j)
  have hbc : Continuous (fun p : A × E => c p.1 ‖p.2‖ • p.2) :=
    ((hcc 0).comp (continuous_fst.prodMk continuous_snd.norm)).smul continuous_snd
  refine ⟨hbc, ?_, ?_⟩
  · intro t htime
    exact smoothGaugeDrift_contDiff (hhs ⟨t, htime⟩) (hhp ⟨t, htime⟩)
      (hvis ⟨t, htime⟩) (hvie ⟨t, htime⟩)
  · have hnear (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t r, |r| ≤ 1 →
        |iteratedDeriv j (c t) r| ≤ C := by
      have hcompact : IsCompact ((univ : Set A) ×ˢ Icc (-1 : ℝ) 1) :=
        isCompact_univ.prod isCompact_Icc
      obtain ⟨C, hCb⟩ := hcompact.exists_bound_of_continuousOn (hcc j).continuousOn
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro t r hr
      have hbval : |iteratedDeriv j (c t) r| ≤ C := by
        simpa only [Real.norm_eq_abs] using hCb (t, r) ⟨mem_univ _, abs_le.mp hr⟩
      exact hbval.trans (le_max_left C 0)
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
    have heq (t : A) (r : ℝ) (hr : 0 < r) :
        c t r = radialGaugeDrift (f t) (v t) r / r := by
      have hh := smoothGaugeDrift_eq_radial (hhs t) (hhp t) (xi := xi t) hr
      rw [hmap, hvelocity] at hh
      apply (eq_div_iff hr.ne').mpr
      simpa only [smoothGaugeDrift, Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul, c] using hh
    have hfar (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t r, 1 ≤ r →
        (1 + r) ^ (1 : ℕ) * |iteratedDeriv j (c t) r| ≤ C := by
      obtain ⟨C, hC, hCb⟩ := raw_intrinsic_drift_coefficient_weighted_jets
        P H G hrotation hT hTlt j
      refine ⟨C, hC, ?_⟩
      intro t r hr
      have hevent : c t =ᶠ[𝓝 r] fun s => radialGaugeDrift (f t) (v t) s / s := by
        filter_upwards [eventually_gt_nhds (lt_of_lt_of_le zero_lt_one hr)] with s hs
        exact heq t s hs
      rw [pow_one, hevent.iteratedDeriv_eq j]
      exact hCb t.1 t.2 r hr
    have hb := even_radial_family_weighted_jets (E := E) hcs hce hnear hfar
    simp only [pow_one] at hb
    intro j
    obtain ⟨C, hC, hCb⟩ := radial_vector_jets_bounded hcs hce hb j
    exact ⟨C, hC, fun t htime => hCb ⟨t, htime⟩⟩

end PoincareConjecture.M35.Uniqueness
