import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicCircle
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicFiber
import Mathlib.Analysis.SpecialFunctions.SmoothTransition









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_polar_circle_diffeomorphs
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (F G : (ℝ × ℝ) × ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFper : ∀ z u s, F ((z, u), s + 2 * Real.pi) = F ((z, u), s) + 2 * Real.pi)
    (hGper : ∀ z u s, G ((z, u), s + 2 * Real.pi) = G ((z, u), s) + 2 * Real.pi)
    (hleft : ∀ z u s, G ((z, u), F ((z, u), s)) = s)
    (hright : ∀ z u s, F ((z, u), G ((z, u), s)) = s)
    {δ : ℝ} (hδ : 0 < δ) (hinner : ∀ z u s, u ≤ δ → F ((z, u), s) = s) :
    ∃ A : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => A p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (A p.1).symm p.2) ∧
      (∀ z x, ‖A z x‖ = ‖x‖ ∧ ‖(A z).symm x‖ = ‖x‖) ∧
      (∀ z r, 0 ≤ r → ∀ s,
        A z (r • (sphereCircleParameter e s : E)) =
          r • (sphereCircleParameter e (F ((z, r ^ 2), s)) : E) ∧
        (A z).symm (r • (sphereCircleParameter e s : E)) =
          r • (sphereCircleParameter e (G ((z, r ^ 2), s)) : E)) ∧
      ∀ z x, (∀ s, F ((z, ‖x‖ ^ 2), s) = s) → A z x = x ∧ (A z).symm x = x := by
  have hT : 0 < 2 * Real.pi := by positivity
  have hrep (x : E) : ∃ s : ℝ, x = ‖x‖ • (sphereCircleParameter e s : E) := by
    by_cases hx : x = 0
    · exact ⟨0, by simp only [hx, norm_zero, zero_smul]⟩
    · obtain ⟨s, hs⟩ := surjective_sphereCircleParameter e (unitRadialProjection q0 x)
      refine ⟨s, ?_⟩
      rw [hs, unitRadialProjection_coe_of_ne_zero q0 hx, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hp : ContDiff ℝ ∞ (fun s : ℝ => (sphereCircleParameter e s : E)) :=
    ((contMDiff_coe_sphere (E := E) (n := 1) (m := ∞)).comp
      (contMDiff_sphereCircleParameter e)).contDiff
  have buildMap (H : (ℝ × ℝ) × ℝ → ℝ) (hH : ContDiff ℝ ∞ H)
      (hper : ∀ z u s, H ((z, u), s + 2 * Real.pi) = H ((z, u), s) + 2 * Real.pi)
      (hsmall : ∀ z u s, u ≤ δ → H ((z, u), s) = s) :
      ∃ U : ℝ × E → E, ContDiff ℝ ∞ U ∧
        (∀ p, ‖U p‖ = ‖p.2‖) ∧
        (∀ z r, 0 ≤ r → ∀ s, U (z, r • (sphereCircleParameter e s : E)) =
          r • (sphereCircleParameter e (H ((z, r ^ 2), s)) : E)) ∧
        ∀ p, (∀ s, H ((p.1, ‖p.2‖ ^ 2), s) = s) → U p = p.2 := by
    let γ : (ℝ × ℝ) → ℝ → E := fun v s => sphereCircleParameter e (H (v, s))
    have hγ : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => γ p.1 p.2) := hp.comp hH
    have hγper (v : ℝ × ℝ) : Periodic (γ v) (2 * Real.pi) := by
      intro s
      change (sphereCircleParameter e (H (v, s + 2 * Real.pi)) : E) = _
      rw [hper v.1 v.2 s]
      exact congrArg Subtype.val (periodic_sphereCircleParameter e (H (v, s)))
    let g : (ℝ × ℝ) → sphere (0 : E) 1 → E := fun v q =>
      periodicCircleCurve (2 * Real.pi) e (γ v) q
    have hg : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
        (fun p : (ℝ × ℝ) × sphere (0 : E) 1 => g p.1 p.2) :=
      contMDiff_periodicCircleCurve_family hT e γ hγ hγper
    have hgrep (v : ℝ × ℝ) (s : ℝ) :
        g v (sphereCircleParameter e s) = (sphereCircleParameter e (H (v, s)) : E) := by
      simpa only [div_self (ne_of_gt hT), one_mul] using
        periodicCircleCurve_sphereCircleParameter hT e (hγper v) s
    have hgnorm (v : ℝ × ℝ) (q : sphere (0 : E) 1) : ‖g v q‖ = 1 := by
      obtain ⟨s, rfl⟩ := surjective_sphereCircleParameter e q
      rw [hgrep]
      exact norm_eq_of_mem_sphere _
    let U : ℝ × E → E := fun p => ‖p.2‖ • g (p.1, ‖p.2‖ ^ 2) (unitRadialProjection q0 p.2)
    have hnorm (p : ℝ × E) : ‖U p‖ = ‖p.2‖ := by
      dsimp only [U]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hgnorm, mul_one]
    have hpolar (z r : ℝ) (hr : 0 ≤ r) (s : ℝ) :
        U (z, r • (sphereCircleParameter e s : E)) =
          r • (sphereCircleParameter e (H ((z, r ^ 2), s)) : E) := by
      by_cases hr0 : r = 0
      · subst r
        simp only [U, zero_smul, norm_zero]
      · have hrpos := lt_of_le_of_ne hr (Ne.symm hr0)
        have hn : ‖r • (sphereCircleParameter e s : E)‖ = r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, norm_eq_of_mem_sphere, mul_one]
        have hproj : unitRadialProjection q0 (r • (sphereCircleParameter e s : E)) =
            sphereCircleParameter e s := by
          apply Subtype.ext
          rw [unitRadialProjection_coe_of_ne_zero q0
            (smul_ne_zero hr0 (ne_zero_of_mem_unit_sphere _)), hn, smul_smul,
            inv_mul_cancel₀ hr0, one_smul]
        change ‖r • (sphereCircleParameter e s : E)‖ •
          g (z, ‖r • (sphereCircleParameter e s : E)‖ ^ 2)
            (unitRadialProjection q0 (r • (sphereCircleParameter e s : E))) = _
        rw [hn, hproj, hgrep]
    have hfix (p : ℝ × E) (hid : ∀ s, H ((p.1, ‖p.2‖ ^ 2), s) = s) : U p = p.2 := by
      obtain ⟨s, hs⟩ := hrep p.2
      calc
        U p = U (p.1, ‖p.2‖ • (sphereCircleParameter e s : E)) :=
          congrArg (fun x => U (p.1, x)) hs
        _ = ‖p.2‖ • (sphereCircleParameter e (H ((p.1, ‖p.2‖ ^ 2), s)) : E) :=
          hpolar p.1 ‖p.2‖ (norm_nonneg _) s
        _ = p.2 := by rw [hid s]; exact hs.symm
    have hU : ContDiff ℝ ∞ U := by
      rw [contDiff_iff_contDiffAt]
      intro p
      by_cases hx : p.2 = 0
      · apply contDiffAt_snd.congr_of_eventuallyEq
        have hnear : ∀ᶠ y : ℝ × E in nhds p, ‖y.2‖ ^ 2 < δ :=
          (continuous_snd.norm.pow 2).continuousAt.eventually_lt continuousAt_const
            (by
              change ‖p.2‖ ^ 2 < δ
              simpa only [hx, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hδ)
        filter_upwards [hnear] with y hy
        exact hfix y (fun s => hsmall y.1 (‖y.2‖ ^ 2) s hy.le)
      · have hq : ContMDiffAt 𝓘(ℝ, ℝ × E) (𝓡 1) ∞
            (fun y : ℝ × E => unitRadialProjection q0 y.2) p :=
          ((contMDiffOn_unitRadialProjection (n := 1) q0).contMDiffAt
            (isClosed_singleton.isOpen_compl.mem_nhds hx)).comp p
              contDiff_snd.contMDiff.contMDiffAt
        have hgu : ContDiffAt ℝ ∞
            (fun y : ℝ × E => g (y.1, ‖y.2‖ ^ 2) (unitRadialProjection q0 y.2)) p :=
          (hg.contMDiffAt.comp p
            ((contDiff_fst.prodMk
              ((contDiff_norm_sq ℝ).comp contDiff_snd)).contMDiff.contMDiffAt.prodMk
              hq)).contDiffAt
        exact ((contDiffAt_norm ℝ hx).comp p contDiffAt_snd).smul hgu
    exact ⟨U, hU, hnorm, hpolar, hfix⟩
  have hGinner (z u s : ℝ) (hu : u ≤ δ) : G ((z, u), s) = s := by
    have h := hleft z u s
    rwa [hinner z u s hu] at h
  obtain ⟨U, hU, hUnorm, hUpolar, hUfix⟩ := buildMap F hF hFper hinner
  obtain ⟨V, hV, hVnorm, hVpolar, hVfix⟩ := buildMap G hG hGper hGinner
  have hVU (z : ℝ) (x : E) : V (z, U (z, x)) = x := by
    obtain ⟨s, hs⟩ := hrep x
    have hu : U (z, x) = ‖x‖ • (sphereCircleParameter e (F ((z, ‖x‖ ^ 2), s)) : E) :=
      (congrArg (fun y => U (z, y)) hs).trans (hUpolar z ‖x‖ (norm_nonneg _) s)
    rw [hu, hVpolar z ‖x‖ (norm_nonneg _) _, hleft]
    exact hs.symm
  have hUV (z : ℝ) (x : E) : U (z, V (z, x)) = x := by
    obtain ⟨s, hs⟩ := hrep x
    have hv : V (z, x) = ‖x‖ • (sphereCircleParameter e (G ((z, ‖x‖ ^ 2), s)) : E) :=
      (congrArg (fun y => V (z, y)) hs).trans (hVpolar z ‖x‖ (norm_nonneg _) s)
    rw [hv, hUpolar z ‖x‖ (norm_nonneg _) _, hright]
    exact hs.symm
  let A : ℝ → (E ≃ₘ[ℝ] E) := fun z =>
    { toEquiv :=
        { toFun := fun x => U (z, x)
          invFun := fun x => V (z, x)
          left_inv := hVU z
          right_inv := hUV z }
      contMDiff_toFun := (hU.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hV.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  refine ⟨A, hU, hV, (fun z x => ⟨hUnorm (z, x), hVnorm (z, x)⟩),
    (fun z r hr s => ⟨hUpolar z r hr s, hVpolar z r hr s⟩), ?_⟩
  intro z x hid
  refine ⟨hUfix (z, x) hid, hVfix (z, x) ?_⟩
  intro s
  have h := hleft z (‖x‖ ^ 2) s
  rwa [hid s] at h




theorem exists_supported_circle_lift_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (B : ℝ × ℝ → ℝ) (hB : ContDiff ℝ ∞ B)
    (hper : ∀ z s, B (z, s + 2 * Real.pi) = B (z, s) + 2 * Real.pi)
    (hpos : ∀ z s, 0 < deriv (fun t => B (z, t)) s) :
    ∃ A : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => A p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (A p.1).symm p.2) ∧
      (∃ K : Set E, IsCompact K ∧ ∀ z x, x ∉ K → A z x = x ∧ (A z).symm x = x) ∧
      (∀ z, HasCompactSupport (fun x => A z x - x) ∧
        HasCompactSupport (fun x => (A z).symm x - x)) ∧
      (∀ z x, ‖A z x‖ = ‖x‖ ∧ ‖(A z).symm x‖ = ‖x‖) ∧
      ∀ z s, A z (sphereCircleParameter e s : E) = (sphereCircleParameter e (B (z, s)) : E) := by
  let κ : ℝ → ℝ := fun u => Real.smoothTransition (4 * u - 1) * Real.smoothTransition (4 - u)
  have hκ : ContDiff ℝ ∞ κ :=
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
        (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))
  have hκrange (u : ℝ) : 0 ≤ κ u ∧ κ u ≤ 1 := by
    have h1 := Real.smoothTransition.nonneg (4 * u - 1)
    have h2 := Real.smoothTransition.nonneg (4 - u)
    have h3 := Real.smoothTransition.le_one (4 * u - 1)
    have h4 := Real.smoothTransition.le_one (4 - u)
    exact ⟨mul_nonneg h1 h2, by dsimp only [κ]; nlinarith⟩
  have hκzero (u : ℝ) (hu : u ≤ 1 / 4 ∨ 4 ≤ u) : κ u = 0 := by
    rcases hu with hu | hu
    · simp only [κ, Real.smoothTransition.zero_of_nonpos (show 4 * u - 1 ≤ 0 by linarith), zero_mul]
    · simp only [κ, Real.smoothTransition.zero_of_nonpos (show 4 - u ≤ 0 by linarith), mul_zero]
  have hκone : κ 1 = 1 := by
    norm_num [κ, Real.smoothTransition.one_of_one_le]
  let H : (ℝ × ℝ) × ℝ → ℝ := fun p => p.2 + κ p.1.2 * (B (p.1.1, p.2) - p.2)
  have hH : ContDiff ℝ ∞ H :=
    contDiff_snd.add ((hκ.comp contDiff_fst.snd).mul
      ((hB.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_snd))
  have hHper (v : ℝ × ℝ) (s : ℝ) : H (v, s + 2 * Real.pi) = H (v, s) + 2 * Real.pi := by
    dsimp only [H]
    rw [hper]
    ring
  have hHpos (v : ℝ × ℝ) (s : ℝ) : 0 < deriv (fun t => H (v, t)) s := by
    have hdB : HasDerivAt (fun t => B (v.1, t)) (deriv (fun t => B (v.1, t)) s) s :=
      ((hB.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) s).hasDerivAt
    have hd := (hasDerivAt_id s).add (((hdB.sub (hasDerivAt_id s))).const_mul (κ v.2))
    change HasDerivAt (fun t => H (v, t)) (1 + κ v.2 * (deriv (fun t => B (v.1, t)) s - 1)) s at hd
    rw [hd.deriv]
    by_cases hk : κ v.2 = 0
    · simp only [hk, zero_mul, add_zero, zero_lt_one]
    · have hm := mul_pos (lt_of_le_of_ne (hκrange v.2).1 (Ne.symm hk)) (hpos v.1 s)
      nlinarith [(hκrange v.2).2]
  obtain ⟨J, hJ, hJI⟩ := exists_smooth_inverse_of_add_period
    (show 0 < 2 * Real.pi by positivity) hH hHper hHpos
  have hHinner (z u s : ℝ) (hu : u ≤ 1 / 4) : H ((z, u), s) = s := by
    simp only [H, hκzero u (Or.inl hu), zero_mul, add_zero]
  obtain ⟨A, hA, hAinv, hAnorm, hApolar, hAfix⟩ := exists_polar_circle_diffeomorphs e q0 H J hH hJ
    (fun z u s => hHper (z, u) s) (fun z u s => (hJI (z, u) s).2.2)
    (fun z u s => (hJI (z, u) s).2.1) (fun z u s => (hJI (z, u) s).1)
    (show (0 : ℝ) < 1 / 4 by norm_num) hHinner
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [Fact.out (p := Module.finrank ℝ E = 2)]
    norm_num)
  have hfix (z : ℝ) (x : E) (hx : x ∉ closedBall (0 : E) 2) : A z x = x ∧ (A z).symm x = x := by
    have hn : 2 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    apply hAfix z x
    intro s
    simp only [H, hκzero (‖x‖ ^ 2) (Or.inr (by nlinarith)), zero_mul, add_zero]
  refine ⟨A, hA, hAinv, ⟨closedBall 0 2, isCompact_closedBall 0 2, hfix⟩, ?_, hAnorm, ?_⟩
  · intro z
    exact ⟨HasCompactSupport.intro (isCompact_closedBall 0 2)
      (fun x hx => sub_eq_zero.mpr (hfix z x hx).1),
      HasCompactSupport.intro (isCompact_closedBall 0 2)
        (fun x hx => sub_eq_zero.mpr (hfix z x hx).2)⟩
  · intro z s
    have h := (hApolar z 1 zero_le_one s).1
    simpa only [one_smul, one_pow, H, hκone, one_mul, add_sub_cancel] using h

end PoincareConjecture.M25.Topology3D
