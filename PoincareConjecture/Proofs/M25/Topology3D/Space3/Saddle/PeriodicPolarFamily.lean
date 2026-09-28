import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CirclePeriodCoordinates
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Module.Equiv

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_periodic_polar_family
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (H : (ℝ × ℝ) × ℝ → ℝ) (hH : ContDiff ℝ ∞ H)
    (hPeriod : ∀ t u s : ℝ,
      H ((t, u), s + 2 * Real.pi) = H ((t, u), s) + 2 * Real.pi)
    (hPositive : ∀ t u s : ℝ,
      0 < deriv (fun a : ℝ => H ((t, u), a)) s)
    (delta : ℝ) (hDelta : 0 < delta)
    (hInner : ∀ t u s : ℝ, u ≤ delta → H ((t, u), s) = s) :
    let p : ℝ → E2 := fun s => J2.symm (Real.cos s, Real.sin s)
    ∃ A : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
      ContDiff ℝ ∞ (fun z : ℝ × E2 => A z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E2 => (A z.1).symm z.2) ∧
      (∀ t : ℝ, ∀ x : E2, ‖A t x‖ = ‖x‖ ∧ ‖(A t).symm x‖ = ‖x‖) ∧
      (∀ t r : ℝ, 0 ≤ r → ∀ s : ℝ,
        A t (r • p s) = r • p (H ((t, r ^ 2), s))) ∧
      (∀ t : ℝ, ∀ x : E2,
        (∀ s : ℝ, H ((t, ‖x‖ ^ 2), s) = s) →
          A t x = x ∧ (A t).symm x = x) := by
  classical
  let T : ℝ := 2 * Real.pi
  have hT : 0 < T := by dsimp [T]; positivity
  have hMono (v : ℝ × ℝ) : StrictMono (fun s => H (v, s)) :=
    strictMono_of_deriv_pos (hPositive v.1 v.2)
  have hSurj (v : ℝ × ℝ) : Surjective (fun s => H (v, s)) := by
    have hNat (n : ℕ) (s : ℝ) : H (v, s + (n : ℝ) * T) = H (v, s) + (n : ℝ) * T := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hPeriod v.1 v.2, ih]
        ring
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt ((|y - H (v, 0)| + 1) / T)
    have hBound : |y - H (v, 0)| + 1 < (n : ℝ) * T := (div_lt_iff₀ hT).mp hn
    have hPlus : H (v, (n : ℝ) * T) = H (v, 0) + (n : ℝ) * T := by simpa using hNat n 0
    have hMinus : H (v, -((n : ℝ) * T)) = H (v, 0) - (n : ℝ) * T := by
      have hh := hNat n (-((n : ℝ) * T))
      rw [neg_add_cancel] at hh
      linarith
    apply intermediate_value_univ (-((n : ℝ) * T)) ((n : ℝ) * T)
      (hH.continuous.comp (continuous_const.prodMk continuous_id))
    change H (v, -((n : ℝ) * T)) ≤ y ∧ y ≤ H (v, (n : ℝ) * T)
    exact ⟨by rw [hMinus]; linarith [neg_abs_le (y - H (v, 0))],
      by rw [hPlus]; linarith [le_abs_self (y - H (v, 0))]⟩
  let B : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun z => (z.1, H z)
  have hB : ContDiff ℝ ∞ B := contDiff_fst.prodMk hH
  have hDiagonal (z : (ℝ × ℝ) × ℝ) : (fderiv ℝ H z) (0, 1) ≠ 0 := by
    have hd := (((hH.differentiable (by simp)) z).hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right z.1 z.2)).hasDerivAt
    have he : deriv (fun s => H (z.1, s)) z.2 = (fderiv ℝ H z) (0, 1) := hd.deriv
    rw [← he]
    exact (hPositive z.1.1 z.1.2 z.2).ne'
  let D : ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) := fun z =>
    (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).skewProd
      (ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 ((fderiv ℝ H z) (0, 1)) (hDiagonal z)))
      ((fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ))
  have hDerivative (z : (ℝ × ℝ) × ℝ) :
      HasFDerivAt B (D z : ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ)) z := by
    have he : (D z : ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ)) =
        (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).prod (fderiv ℝ H z) := by
      apply ContinuousLinearMap.ext
      intro w
      apply Prod.ext
      · rfl
      · change w.2 * (fderiv ℝ H z) (0, 1) + (fderiv ℝ H z) (w.1, 0) = (fderiv ℝ H z) w
        have hs : (fderiv ℝ H z) (0, w.2) = w.2 * (fderiv ℝ H z) (0, 1) := by
          simpa using (fderiv ℝ H z).map_smul w.2 (0, 1)
        rw [← hs, ← map_add]
        simp
    rw [he]
    exact hasFDerivAt_fst.prodMk ((hH.differentiable (by simp)) z).hasFDerivAt
  have hBij : Bijective B := by
    constructor
    · rintro ⟨v, s⟩ ⟨w, t⟩ he
      have hvw : v = w := congrArg Prod.fst he
      subst w
      exact Prod.ext rfl ((hMono v).injective (congrArg Prod.snd he))
    · rintro ⟨v, s⟩
      obtain ⟨t, ht⟩ := hSurj v s
      exact ⟨(v, t), Prod.ext rfl ht⟩
  have hOpen : IsOpenMap B := isOpenMap_of_hasStrictFDerivAt_equiv
    (fun z => hB.contDiffAt.hasStrictFDerivAt' (hDerivative z) (by simp))
  let eB : ((ℝ × ℝ) × ℝ) ≃ₜ ((ℝ × ℝ) × ℝ) :=
    (Equiv.ofBijective B hBij).toHomeomorphOfContinuousOpen hB.continuous hOpen
  have hInv : ContDiff ℝ ∞ eB.symm := eB.contDiff_symm hDerivative hB
  let G : (ℝ × ℝ) × ℝ → ℝ := fun z => (eB.symm z).2
  have hG : ContDiff ℝ ∞ G := hInv.snd
  have hInvFirst (z : (ℝ × ℝ) × ℝ) : (eB.symm z).1 = z.1 := by
    have hh := congrArg Prod.fst (eB.apply_symm_apply z)
    change (eB.symm z).1 = z.1 at hh
    exact hh
  have hHG (v : ℝ × ℝ) (s : ℝ) : H (v, G (v, s)) = s := by
    have he := congrArg Prod.snd (eB.apply_symm_apply (v, s))
    change H ((eB.symm (v, s)).1, G (v, s)) = s at he
    rwa [hInvFirst] at he
  have hGH (v : ℝ × ℝ) (s : ℝ) : G (v, H (v, s)) = s :=
    congrArg Prod.snd (eB.symm_apply_apply (v, s))
  have hGPeriod (t u s : ℝ) : G ((t, u), s + T) = G ((t, u), s) + T := by
    apply (hMono (t, u)).injective
    change H ((t, u), G ((t, u), s + T)) = H ((t, u), G ((t, u), s) + T)
    rw [hHG, hPeriod t u, hHG]
  have hGInner (t u s : ℝ) (hu : u ≤ delta) : G ((t, u), s) = s := by
    have hh := hGH (t, u) s
    rwa [hInner t u s hu] at hh
  let e : ℂ ≃ₗᵢ[ℝ] E2 :=
    { toLinearEquiv := Complex.equivRealProdCLM.toLinearEquiv.trans J2.symm.toLinearEquiv
      norm_map' := by
        intro z
        have hz := hJ2 (J2.symm (z.re, z.im))
        rw [J2.apply_symm_apply] at hz
        have hc := Complex.sq_norm z
        simp only [Complex.normSq_apply] at hc
        change ‖J2.symm (z.re, z.im)‖ = ‖z‖
        nlinarith [norm_nonneg (J2.symm (z.re, z.im)), norm_nonneg z] }
  let J : Circle ≃ₜ UnitCircle := e.toHomeomorph.subtype (fun z => by
    change z ∈ sphere (0 : ℂ) 1 ↔ e z ∈ sphere (0 : E2) 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm, e.norm_map])
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hJi : ContMDiff (𝓡 1) (𝓡 1) ∞ J.symm := by
    have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (fun z : UnitCircle => (z : E2)) := contMDiff_coe_sphere
    exact (e.symm.contDiff.contMDiff.comp hcoe).codRestrict_sphere _
  let p : ℝ → E2 := fun s => J2.symm (Real.cos s, Real.sin s)
  let q : ℝ → UnitCircle := fun s => J (Circle.exp s)
  have hqp (s : ℝ) : (q s : E2) = p s := by
    change J2.symm (Complex.equivRealProdCLM (Circle.exp s : ℂ)) = J2.symm (Real.cos s, Real.sin s)
    congr 1
    apply Prod.ext
    · simp [Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re]
    · simp [Circle.coe_exp, Complex.exp_mul_I, Complex.sin_ofReal_re]
  have hp : ContDiff ℝ ∞ p := J2.symm.contDiff.comp (contDiff_id.cos.prodMk contDiff_id.sin)
  have hpNorm (s : ℝ) : ‖p s‖ = 1 := by rw [← hqp]; exact norm_eq_of_mem_sphere _
  have hpPeriod : Periodic p T := by
    intro s
    simp only [p, T, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hqSurj : Surjective q := by
    intro x
    obtain ⟨s, hs⟩ := Circle.exp_surjective (J.symm x)
    exact ⟨s, (congrArg J hs).trans (J.apply_symm_apply x)⟩
  let L : AddCircle T ≃ₜ UnitCircle := (AddCircle.homeomorphCircle hT.ne').trans J
  have hL (s : ℝ) : L (s : AddCircle T) = q s := by
    change J (AddCircle.homeomorphCircle hT.ne' (s : AddCircle T)) = _
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    simp only [T, div_self (show 2 * Real.pi ≠ 0 by positivity), one_mul, q]
  let Q : UnitCircle ≃ₜ UnitCircle := J.symm.trans complexUnitCircleHomeomorph
  have hQ : ContMDiff (𝓡 1) (𝓡 1) ∞ Q := complexUnitCircleHomeomorph_contMDiff.comp hJi
  have hQq (s : ℝ) : Q (q s) = periodCircleParam T s := by
    change complexUnitCircleHomeomorph (J.symm (J (Circle.exp s))) = _
    rw [J.symm_apply_apply]
    simp only [periodCircleParam, T, div_self (show 2 * Real.pi ≠ 0 by positivity), one_mul]
  have hLocal (x : UnitCircle) : ∃ s : UnitCircle → ℝ,
      ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ s x ∧ q ∘ s = id := by
    obtain ⟨s, hs, hsection⟩ := exists_periodCircle_local_time T hT.ne' (Q x)
    refine ⟨s ∘ Q, hs.comp x hQ.contMDiffAt, ?_⟩
    funext y
    apply Q.injective
    change Q (q (s (Q y))) = Q y
    rw [hQq]
    exact congrFun hsection (Q y)
  have hRep (x : E2) : ∃ s : ℝ, x = ‖x‖ • p s := by
    obtain ⟨s, hs⟩ := hqSurj (circleDirection x)
    refine ⟨s, ?_⟩
    calc
      x = ‖x‖ • (circleDirection x : E2) := (circleDirection_norm_smul x).symm
      _ = ‖x‖ • p s := by rw [← hs, hqp]
  have buildMap (K : (ℝ × ℝ) × ℝ → ℝ) (hK : ContDiff ℝ ∞ K)
      (hPer : ∀ t u s : ℝ, K ((t, u), s + T) = K ((t, u), s) + T)
      (hSmall : ∀ t u s : ℝ, u ≤ delta → K ((t, u), s) = s) :
      ∃ U : ℝ × E2 → E2, ContDiff ℝ ∞ U ∧
        (∀ z, ‖U z‖ = ‖z.2‖) ∧
        (∀ t r : ℝ, 0 ≤ r → ∀ s : ℝ,
          U (t, r • p s) = r • p (K ((t, r ^ 2), s))) ∧
        (∀ z : ℝ × E2, (∀ s : ℝ, K ((z.1, ‖z.2‖ ^ 2), s) = s) → U z = z.2) := by
    let gamma : (ℝ × ℝ) → ℝ → E2 := fun v s => p (K (v, s))
    have hGamma : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => gamma z.1 z.2) := hp.comp hK
    have hGammaPer (v : ℝ × ℝ) : Periodic (gamma v) T := by
      intro s
      change p (K ((v.1, v.2), s + T)) = p (K ((v.1, v.2), s))
      rw [hPer, hpPeriod]
    let g : (ℝ × ℝ) → UnitCircle → E2 := fun v x => (hGammaPer v).lift (L.symm x)
    have hgq (v : ℝ × ℝ) (s : ℝ) : g v (q s) = p (K (v, s)) := by
      change (hGammaPer v).lift (L.symm (q s)) = _
      rw [← hL s, L.symm_apply_apply]
      exact Function.Periodic.lift_coe (hGammaPer v) s
    have hgNorm (v : ℝ × ℝ) (x : UnitCircle) : ‖g v x‖ = 1 := by
      obtain ⟨s, rfl⟩ := hqSurj x
      rw [hgq]
      exact hpNorm _
    have hg : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun z : (ℝ × ℝ) × UnitCircle => g z.1 z.2) := by
      intro z
      obtain ⟨s, hs, hsection⟩ := hLocal z.2
      have hPair : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (𝓡 1)) 𝓘(ℝ, (ℝ × ℝ) × ℝ) ∞
          (fun w : (ℝ × ℝ) × UnitCircle => (w.1, s w.2)) z :=
        contMDiffAt_fst.prodMk_space (hs.comp z contMDiffAt_snd)
      apply (hGamma.contMDiff.contMDiffAt.comp z hPair).congr_of_eventuallyEq
      exact Eventually.of_forall (fun w => by
        have hh := hgq w.1 (s w.2)
        rw [show q (s w.2) = w.2 from congrFun hsection w.2] at hh
        exact hh)
    let U : ℝ × E2 → E2 := fun z => ‖z.2‖ • g (z.1, ‖z.2‖ ^ 2) (circleDirection z.2)
    have hNorm (z : ℝ × E2) : ‖U z‖ = ‖z.2‖ := by
      simp only [U, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hgNorm, mul_one]
    have hPolar (t r : ℝ) (hr : 0 ≤ r) (s : ℝ) :
        U (t, r • p s) = r • p (K ((t, r ^ 2), s)) := by
      by_cases hr0 : r = 0
      · subst r
        simp only [U, zero_smul, norm_zero]
      · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
        have hn : ‖r • p s‖ = r := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hpNorm, mul_one]
        have hDir : circleDirection (r • p s) = q s := by
          rw [← hqp]
          exact circleDirection_smul (q s) hrpos
        change ‖r • p s‖ • g (t, ‖r • p s‖ ^ 2) (circleDirection (r • p s)) = _
        rw [hn, hDir, hgq]
    have hFix (z : ℝ × E2) (hz : ∀ s : ℝ, K ((z.1, ‖z.2‖ ^ 2), s) = s) : U z = z.2 := by
      obtain ⟨s, hs⟩ := hRep z.2
      calc
        U z = U (z.1, ‖z.2‖ • p s) := congrArg (fun x => U (z.1, x)) hs
        _ = ‖z.2‖ • p (K ((z.1, ‖z.2‖ ^ 2), s)) := hPolar z.1 ‖z.2‖ (norm_nonneg _) s
        _ = z.2 := by rw [hz s]; exact hs.symm
    have hSmooth : ContDiff ℝ ∞ U := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z.2 = 0
      · have hNear : ∀ᶠ w : ℝ × E2 in 𝓝 z, ‖w.2‖ ^ 2 < delta :=
          (continuous_snd.norm.pow 2).continuousAt.eventually_lt continuousAt_const
            (by
              change ‖z.2‖ ^ 2 < delta
              simpa only [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hDelta)
        apply contDiffAt_snd.congr_of_eventuallyEq
        filter_upwards [hNear] with w hw
        exact hFix w (fun s => hSmall w.1 (‖w.2‖ ^ 2) s hw.le)
      · have hDir : ContMDiffAt 𝓘(ℝ, ℝ × E2) (𝓡 1) ∞
            (fun w : ℝ × E2 => circleDirection w.2) z :=
          (circleDirection_contMDiffOn.contMDiffAt
            (isClosed_singleton.isOpen_compl.mem_nhds hz)).comp z
              contDiff_snd.contMDiff.contMDiffAt
        have hPair : ContMDiffAt 𝓘(ℝ, ℝ × E2) (𝓘(ℝ, ℝ × ℝ).prod (𝓡 1)) ∞
            (fun w : ℝ × E2 => ((w.1, ‖w.2‖ ^ 2), circleDirection w.2)) z :=
          ((contDiff_fst.prodMk
            ((contDiff_norm_sq ℝ).comp contDiff_snd)).contMDiff.contMDiffAt).prodMk hDir
        have hGAt : ContDiffAt ℝ ∞ (fun w : ℝ × E2 =>
            g (w.1, ‖w.2‖ ^ 2) (circleDirection w.2)) z :=
          (hg.contMDiffAt.comp z hPair).contDiffAt
        exact ((contDiffAt_norm ℝ hz).comp z contDiffAt_snd).smul hGAt
    exact ⟨U, hSmooth, hNorm, hPolar, hFix⟩
  obtain ⟨U, hU, hUNorm, hUPolar, hUFix⟩ := buildMap H hH hPeriod hInner
  obtain ⟨V, hV, hVNorm, hVPolar, hVFix⟩ := buildMap G hG hGPeriod hGInner
  have hVU (t : ℝ) (x : E2) : V (t, U (t, x)) = x := by
    obtain ⟨s, hs⟩ := hRep x
    have hu : U (t, x) = ‖x‖ • p (H ((t, ‖x‖ ^ 2), s)) :=
      (congrArg (fun y => U (t, y)) hs).trans (hUPolar t ‖x‖ (norm_nonneg _) s)
    rw [hu, hVPolar t ‖x‖ (norm_nonneg _) _, hGH]
    exact hs.symm
  have hUV (t : ℝ) (x : E2) : U (t, V (t, x)) = x := by
    obtain ⟨s, hs⟩ := hRep x
    have hv : V (t, x) = ‖x‖ • p (G ((t, ‖x‖ ^ 2), s)) :=
      (congrArg (fun y => V (t, y)) hs).trans (hVPolar t ‖x‖ (norm_nonneg _) s)
    rw [hv, hUPolar t ‖x‖ (norm_nonneg _) _, hHG]
    exact hs.symm
  let A : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ := fun t =>
    { toEquiv :=
        { toFun := fun x => U (t, x)
          invFun := fun x => V (t, x)
          left_inv := hVU t
          right_inv := hUV t }
      contMDiff_toFun := (hU.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hV.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  refine ⟨A, hU, hV, (fun t x => ⟨hUNorm (t, x), hVNorm (t, x)⟩), hUPolar, ?_⟩
  intro t x hx
  refine ⟨hUFix (t, x) hx, hVFix (t, x) ?_⟩
  intro s
  have hh := hGH (t, ‖x‖ ^ 2) s
  rwa [hx s] at hh

end PoincareConjecture.M25.Topology3D
