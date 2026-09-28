import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedPolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SmoothCircleLift









set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D



def complexEdgeDet (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re



theorem roundedCorner_det_pos (p u v : ℂ) {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hρ : Differentiable ℝ ρ)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hder : ∀ t, |deriv ρ t| ≤ 1)
    (hsmall : 5 * δ * (|complexEdgeDet u v| + 1) <
      min (complexEdgeDet p u) (complexEdgeDet p v)) (t : ℝ) :
    0 < complexEdgeDet (roundedCorner ρ p u v t) (deriv (roundedCorner ρ p u v) t) := by
  have herror : |t * deriv ρ t - ρ t| ≤ 5 * δ := by
    by_cases ht : |t| ≤ 2 * δ
    · calc
        |t * deriv ρ t - ρ t| ≤ |t * deriv ρ t| + |ρ t| := abs_sub _ _
        _ = |t| * |deriv ρ t| + ρ t := by
          rw [abs_mul, abs_of_nonneg ((abs_nonneg t).trans (hbound t).1)]
        _ ≤ |t| * 1 + (|t| + δ) :=
          add_le_add (mul_le_mul_of_nonneg_left (hder t) (abs_nonneg t)) (hbound t).2
        _ ≤ 5 * δ := by linarith
    · have htδ : δ < |t| := by linarith
      have hrhot : ρ t = |t| := htail t htδ.le
      by_cases ht0 : 0 ≤ t
      · have hdt : δ < t := by simpa only [abs_of_nonneg ht0] using htδ
        have heq : ρ =ᶠ[𝓝 t] (fun s : ℝ => s) := by
          filter_upwards [isOpen_Ioi.mem_nhds hdt] with s hs
          have hs0 : 0 < s := hδ.trans hs
          rw [htail s (by rw [abs_of_pos hs0]; exact hs.le), abs_of_pos hs0]
        have hd : deriv ρ t = 1 := ((hasDerivAt_id t).congr_of_eventuallyEq heq).deriv
        rw [hd, mul_one, hrhot, abs_of_nonneg ht0, sub_self, abs_zero]
        positivity
      · have hdt : t < -δ := by rw [abs_of_neg (lt_of_not_ge ht0)] at htδ; linarith
        have heq : ρ =ᶠ[𝓝 t] (fun s : ℝ => -s) := by
          filter_upwards [isOpen_Iio.mem_nhds hdt] with s hs
          have hs' : s < -δ := hs
          have hs0 : s < 0 := by linarith
          rw [htail s (by rw [abs_of_neg hs0]; linarith), abs_of_neg hs0]
        have hd : deriv ρ t = -1 := ((hasDerivAt_id t).neg.congr_of_eventuallyEq heq).deriv
        rw [hd, hrhot, abs_of_neg (lt_of_not_ge ht0)]
        simp only [mul_neg_one, sub_self, abs_zero]
        positivity
  let a := (1 - deriv ρ t) / 2
  let b := (1 + deriv ρ t) / 2
  let ε := min (complexEdgeDet p u) (complexEdgeDet p v)
  have ha : 0 ≤ a := by dsimp [a]; linarith [(abs_le.mp (hder t)).2]
  have hb : 0 ≤ b := by dsimp [b]; linarith [(abs_le.mp (hder t)).1]
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hmain : ε ≤ a * complexEdgeDet p u + b * complexEdgeDet p v := by
    have hu := mul_le_mul_of_nonneg_left (min_le_left (complexEdgeDet p u)
      (complexEdgeDet p v)) ha
    have hv := mul_le_mul_of_nonneg_left (min_le_right (complexEdgeDet p u)
      (complexEdgeDet p v)) hb
    change a * ε ≤ a * complexEdgeDet p u at hu
    change b * ε ≤ b * complexEdgeDet p v at hv
    calc
      ε = (a + b) * ε := by rw [hab, one_mul]
      _ = a * ε + b * ε := by ring
      _ ≤ a * complexEdgeDet p u + b * complexEdgeDet p v := add_le_add hu hv
  have hk : |(t * deriv ρ t - ρ t) / 2 * complexEdgeDet u v| ≤
      (5 * δ / 2) * |complexEdgeDet u v| := by
    rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right herror (by norm_num)) (abs_nonneg _)
  have hpos : 0 < ε :=
    (mul_pos (mul_pos (by norm_num) hδ) (by positivity)).trans hsmall
  have herr : (5 * δ / 2) * |complexEdgeDet u v| < ε / 2 := by
    change 5 * δ * (|complexEdgeDet u v| + 1) < ε at hsmall
    nlinarith
  have hformula : complexEdgeDet (roundedCorner ρ p u v t)
      (deriv (roundedCorner ρ p u v) t) =
      a * complexEdgeDet p u + b * complexEdgeDet p v +
        (t * deriv ρ t - ρ t) / 2 * complexEdgeDet u v := by
    rw [(hasDerivAt_roundedCorner p u v (hρ t)).deriv]
    simp only [complexEdgeDet, roundedCorner, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul, a, b]
    ring
  rw [hformula]
  linarith [(abs_le.mp hk).1]



theorem exists_roundedPolygon_det_threshold {n : ℕ} [NeZero n] (p : Polygon ℂ n)
    (hp : ∀ i, 0 < complexEdgeDet (p i) (p (finRotate n i))) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ < d → ∀ ρ : ℝ → ℝ,
      Differentiable ℝ ρ → (∀ t, δ ≤ |t| → ρ t = |t|) →
      (∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ) → (∀ t, |deriv ρ t| ≤ 1) →
      ∀ t, 0 < complexEdgeDet (roundedPolygonParameter ρ p t)
        (deriv (roundedPolygonParameter ρ p) t) := by
  let u (i : Fin n) := p i - p ((finRotate n).symm i)
  let v (i : Fin n) := p (finRotate n i) - p i
  have hu (i : Fin n) : 0 < complexEdgeDet (p i) (u i) := by
    have heq : complexEdgeDet (p i) (u i) =
        complexEdgeDet (p ((finRotate n).symm i)) (p i) := by
      simp only [u, complexEdgeDet, Complex.sub_re, Complex.sub_im]
      ring
    rw [heq]
    simpa only [Equiv.apply_symm_apply] using hp ((finRotate n).symm i)
  have hv (i : Fin n) : 0 < complexEdgeDet (p i) (v i) := by
    have heq : complexEdgeDet (p i) (v i) = complexEdgeDet (p i) (p (finRotate n i)) := by
      simp only [v, complexEdgeDet, Complex.sub_re, Complex.sub_im]
      ring
    rw [heq]
    exact hp i
  let d (i : Fin n) := min (complexEdgeDet (p i) (u i)) (complexEdgeDet (p i) (v i)) /
    (5 * (|complexEdgeDet (u i) (v i)| + 1))
  have hd (i : Fin n) : 0 < d i := div_pos (lt_min (hu i) (hv i)) (by positivity)
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  refine ⟨min (1 / 4) (d j), lt_min (by norm_num) (hd j), ?_⟩
  intro δ hδ hδd ρ hρ htail hbound hder t
  have hquarter : δ < 1 / 4 := lt_of_lt_of_le hδd (min_le_left _ _)
  have hhalf : δ < 1 / 2 := by linarith
  have hsmall (i : Fin n) : 5 * δ * (|complexEdgeDet (u i) (v i)| + 1) <
      min (complexEdgeDet (p i) (u i)) (complexEdgeDet (p i) (v i)) := by
    have hh : δ < d i := (lt_of_lt_of_le hδd (min_le_right _ _)).trans_le
      (hj i (Finset.mem_univ i))
    have hm := (lt_div_iff₀ (show 0 < 5 * (|complexEdgeDet (u i) (v i)| + 1) by positivity)).mp hh
    nlinarith
  let P : ℤ → ℂ := fun k => p (polygonIntegerIndex n k)
  let i : ℤ := ⌊t + 1 / 2⌋
  have hlo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hhi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
    constructor <;> linarith
  have hprev : polygonIntegerIndex n (i - 1) =
      (finRotate n).symm (polygonIntegerIndex n i) := by
    apply (finRotate n).injective
    rw [← polygonIntegerIndex_succ, sub_add_cancel, Equiv.apply_symm_apply]
  let Γ := roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i)
  have hΓ := hasDerivAt_roundedCorner (P i) (P i - P (i - 1)) (P (i + 1) - P i) (hρ (t - i))
  have hΓ' : HasDerivAt Γ (deriv Γ (t - i)) (t - i) := hΓ.congr_deriv hΓ.deriv.symm
  have htrans : HasDerivAt (fun s : ℝ => Γ (s - i)) (deriv Γ (t - i)) t := by
    simpa only [Function.comp_def, one_smul, id_eq] using
      hΓ'.scomp t ((hasDerivAt_id t).sub_const (i : ℝ))
  have hactual : HasDerivAt (roundedPolygonParameter ρ p) (deriv Γ (t - i)) t := by
    apply htrans.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact roundedVertexPath_eq_local P hδ hhalf htail hbound i hs
  rw [hactual.deriv]
  change 0 < complexEdgeDet (Γ (t - i)) (deriv Γ (t - i))
  apply roundedCorner_det_pos (P i) (P i - P (i - 1)) (P (i + 1) - P i)
    hδ hρ htail hbound hder
  simpa only [P, hprev, polygonIntegerIndex_succ, u, v] using hsmall (polygonIntegerIndex n i)




theorem exists_positive_polar_representation (γ : ℝ → ℂ)
    (hγ : ContDiff ℝ ∞ γ) (hangular : ∀ t, 0 < complexEdgeDet (γ t) (deriv γ t))
    {T : ℝ} (hper : Periodic γ T) (hinj : InjOn γ (Ico 0 T)) :
    ∃ B r : ℝ → ℝ, ContDiff ℝ ∞ B ∧ ContDiff ℝ ∞ r ∧
      (∀ t, 0 < deriv B t) ∧ (∀ t, 0 < r t) ∧ Periodic r T ∧
      Periodic (fun t => sphereCircleParameter (LinearIsometryEquiv.refl ℝ ℂ) (B t)) T ∧
      (∀ t, γ t = r t •
        (sphereCircleParameter (LinearIsometryEquiv.refl ℝ ℂ) (B t) : ℂ)) ∧
      InjOn (fun t => r t •
        (sphereCircleParameter (LinearIsometryEquiv.refl ℝ ℂ) (B t) : ℂ)) (Ico 0 T) := by
  have hne (t : ℝ) : γ t ≠ 0 := by
    intro hz
    have h := hangular t
    simp only [hz, complexEdgeDet, Complex.zero_re, Complex.zero_im,
      zero_mul, sub_self, lt_self_iff_false] at h
  let r : ℝ → ℝ := fun t => ‖γ t‖
  have hrpos (t : ℝ) : 0 < r t := norm_pos_iff.mpr (hne t)
  have hr : ContDiff ℝ ∞ r := by
    rw [contDiff_iff_contDiffAt]
    exact fun t => hγ.contDiffAt.norm ℝ (hne t)
  let N : ℝ → ℂ := fun t => (r t)⁻¹ • γ t
  have hN : ContDiff ℝ ∞ N := (hr.inv (fun t => (hrpos t).ne')).smul hγ
  have hNnorm (t : ℝ) : ‖N t‖ = 1 := by
    dsimp only [N]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hrpos t).le)]
    exact inv_mul_cancel₀ (hrpos t).ne'
  let e := LinearIsometryEquiv.refl ℝ ℂ
  obtain ⟨s0, hs0⟩ := surjective_sphereCircleParameter e
    ⟨N 0, mem_sphere_zero_iff_norm.mpr (hNnorm 0)⟩
  obtain ⟨B, hB, _, hBN⟩ := exists_contDiff_sphere_parameter_lift e N hN hNnorm
    0 s0 (congrArg Subtype.val hs0)
  have hrepr (t : ℝ) : γ t = r t • (sphereCircleParameter e (B t) : ℂ) := by
    rw [hBN]
    dsimp only [N]
    rw [smul_smul, mul_inv_cancel₀ (hrpos t).ne', one_smul]
  have hBpos (t : ℝ) : 0 < deriv B t := by
    let q : ℂ := sphereCircleParameter e (B t)
    have hq : HasDerivAt (fun s => (sphereCircleParameter e (B s) : ℂ))
        (deriv B t • (Complex.I * q)) t := by
      exact (hasDerivAt_sphereCircleParameter_coe e (B t)).scomp t
        ((hB.differentiable (by simp)) t).hasDerivAt
    have hD : deriv γ t = deriv r t • q + r t • (deriv B t • (Complex.I * q)) := by
      have h := (((hr.differentiable (by simp)) t).hasDerivAt.smul hq).deriv
      change deriv (fun s => r s • (sphereCircleParameter e (B s) : ℂ)) t =
        r t • (deriv B t • (Complex.I * q)) + deriv r t • q at h
      rw [show (fun s => r s • (sphereCircleParameter e (B s) : ℂ)) = γ from
        funext fun s => (hrepr s).symm] at h
      simpa only [add_comm] using h
    have hunit : q.re ^ 2 + q.im ^ 2 = 1 := by
      have h := Circle.normSq_coe (Circle.exp (B t))
      change q.re * q.re + q.im * q.im = 1 at h
      nlinarith
    have hdet : complexEdgeDet (γ t) (deriv γ t) = r t ^ 2 * deriv B t := by
      rw [hD, hrepr t]
      change complexEdgeDet (r t • q)
        (deriv r t • q + r t • (deriv B t • (Complex.I * q))) = _
      have heq : complexEdgeDet (r t • q)
          (deriv r t • q + r t • (deriv B t • (Complex.I * q))) =
          r t ^ 2 * deriv B t * (q.re ^ 2 + q.im ^ 2) := by
        simp only [complexEdgeDet, Complex.smul_re, Complex.smul_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, smul_eq_mul]
        ring
      rw [heq, hunit, mul_one]
    have hp := hangular t
    rw [hdet] at hp
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (hrpos t))).mp hp
  have hrper : Periodic r T := fun t => congrArg norm (hper t)
  refine ⟨B, r, hB, hr, hBpos, hrpos, hrper, ?_, hrepr, ?_⟩
  · intro t
    apply Subtype.ext
    rw [hBN, hBN]
    dsimp only [N]
    rw [hrper, hper]
  · intro s hs t ht heq
    apply hinj hs ht
    rw [hrepr s, hrepr t]
    exact heq

end PoincareConjecture.M25.Topology3D
