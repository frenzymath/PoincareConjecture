import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedPeriodInitialApproximation
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem exists_smooth_positive_constantSpeed_C2_approximation
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) {U : Set W} (hU : IsOpen U)
    (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {t : ℝ} (ht : t ∈ Icc a b) {L0 : ℝ} (hL0 : 0 < L0)
    {γ : ℝ → M} (hγp : Function.Periodic γ L0)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 γ)
    (himm : ∀ x, curveVelocity (n := n) γ x ≠ 0)
    {v0 : ℝ} (hv0 : 0 < v0)
    (hspeed : ∀ x, curveSpeed F (fun y _ => γ y) t x = v0)
    {eps : ℝ} (heps : 0 < eps) :
    let c := fun x => e (γ x)
    ∃ r : ℝ → W, ∃ m : ℝ, 0 < m ∧ |m - v0| < eps ∧
      ContDiff ℝ ∞ r ∧ Function.Periodic r L0 ∧
      (∀ x, r x ∈ U ∧ e (ρ (r x)) = r x) ∧
      (∀ x, mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r x) (deriv r x) ≠ 0) ∧
      (∀ x, curveSpeed F (fun y _ => ρ (r y)) t x = m) ∧
      ∀ x, ‖r x - c x‖ < eps ∧ ‖deriv r x - deriv c x‖ < eps ∧
        ‖deriv (deriv r) x - deriv (deriv c) x‖ < eps := by
  let gamma := fun x : ℝ => γ (x / v0)
  have hinv (x : ℝ) : HasDerivAt (fun y : ℝ => y / v0) (1 / v0) x :=
    (hasDerivAt_id x).div_const v0
  have hinvc : ContDiff ℝ 2 (fun x : ℝ => x / v0) := contDiff_id.div_const v0
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma := hγ.comp hinvc.contMDiff
  have hgammap : Function.Periodic gamma (v0 * L0) := by
    intro x
    change γ ((x + v0 * L0) / v0) = γ (x / v0)
    have harg : (x + v0 * L0) / v0 = x / v0 + L0 := by
      field_simp
    rw [harg]
    exact hγp (x / v0)
  have hgammav (x : ℝ) : curveVelocity (n := n) gamma x =
      (1 / v0) • curveVelocity (n := n) γ (x / v0) :=
    curveVelocity_comp (hγ.mdifferentiable (by norm_num) _) (hinv x)
  have hgammaimm (x : ℝ) : curveVelocity (n := n) gamma x ≠ 0 := by
    rw [hgammav]
    exact smul_ne_zero (one_div_pos.mpr hv0).ne' (himm _)
  have hunit (x : ℝ) : curveSpeed F (fun y _ => gamma y) t x = 1 := by
    change curveSpeed F (fun y _ => γ (y / v0)) t x = 1
    rw [curveSpeed_comp F (fun y _ => γ y)
      (hγ.mdifferentiable (by norm_num) _) (hinv x) (one_div_pos.mpr hv0).le,
      hspeed]
    exact one_div_mul_cancel hv0.ne'
  let D := 1 + v0 + v0 ^ 2
  let delta := eps / D
  have hD : 0 < D := by dsimp only [D]; positivity
  have hdelta : 0 < delta := div_pos heps hD
  have hDdelta : D * delta = eps := mul_div_cancel₀ _ hD.ne'
  have hsmall (z : ℝ) (hz : z < D) : z * delta < eps :=
    (mul_lt_mul_of_pos_right hz hdelta).trans_eq hDdelta
  have hsmall0 : delta < eps := by
    simpa only [one_mul] using
      hsmall 1 (by dsimp only [D]; nlinarith only [hv0, sq_nonneg v0])
  have hsmall1 : v0 * delta < eps :=
    hsmall v0 (by dsimp only [D]; nlinarith only [sq_nonneg v0])
  have hsmall2 : v0 ^ 2 * delta < eps :=
    hsmall (v0 ^ 2) (by dsimp only [D]; linarith only [hv0])
  obtain ⟨rhat, mhat, hmhat, hmsmall, hrhat, hrhatp, hrhatfix,
      hrhatimm, hrhatspeed, hnear⟩ :=
    exists_smooth_constantSpeed_fixedPeriod_C2_approximation F he hU heU hρ hρe ht
      (mul_pos hv0 hL0) hgammap hgamma hgammaimm hunit hdelta
  let chat := fun x => e (gamma x)
  let c := fun x => e (γ x)
  let r := fun x => rhat (v0 * x)
  let m := v0 * mhat
  have hchat : ContDiff ℝ 2 chat :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hgamma).contDiff
  have hlin (x : ℝ) : HasDerivAt (fun y : ℝ => v0 * y) v0 x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul v0
  have hscaled (f : ℝ → W) (hf : ContDiff ℝ 2 f) :
      (∀ x, deriv (fun y => f (v0 * y)) x = v0 • deriv f (v0 * x)) ∧
      ∀ x, deriv (deriv (fun y => f (v0 * y))) x =
        v0 ^ 2 • deriv (deriv f) (v0 * x) := by
    have hfirst (x : ℝ) : deriv (fun y => f (v0 * y)) x =
        v0 • deriv f (v0 * x) :=
      ((hf.differentiable (by norm_num) _).hasDerivAt.scomp x (hlin x)).deriv
    refine ⟨hfirst, ?_⟩
    have heq : deriv (fun y => f (v0 * y)) = fun x => v0 • deriv f (v0 * x) :=
      funext hfirst
    intro x
    rw [heq]
    have hd := ((hf.differentiable_deriv_two _).hasDerivAt.scomp x (hlin x)).fun_const_smul v0
    simpa only [Function.comp_def, smul_smul, pow_two] using hd.deriv
  have hcc : c = fun x => chat (v0 * x) := by
    funext x
    dsimp only [c, chat, gamma]
    rw [mul_div_cancel_left₀ x hv0.ne']
  have hrjets := hscaled rhat
    (hrhat.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hcjets := hscaled chat hchat
  have hr1 (x : ℝ) : deriv r x = v0 • deriv rhat (v0 * x) := hrjets.1 x
  have hr2 (x : ℝ) : deriv (deriv r) x =
      v0 ^ 2 • deriv (deriv rhat) (v0 * x) := hrjets.2 x
  have hc1 (x : ℝ) : deriv c x = v0 • deriv chat (v0 * x) := by
    rw [hcc]
    exact hcjets.1 x
  have hc2 (x : ℝ) : deriv (deriv c) x =
      v0 ^ 2 • deriv (deriv chat) (v0 * x) := by
    rw [hcc]
    exact hcjets.2 x
  have hmspeed : |m - v0| < eps := by
    have heq : m - v0 = v0 * (mhat - 1) := by dsimp only [m]; ring
    rw [heq, abs_mul, abs_of_pos hv0]
    exact (mul_lt_mul_of_pos_left hmsmall hv0).trans hsmall1
  have hr : ContDiff ℝ ∞ r := hrhat.comp (contDiff_const.mul contDiff_id)
  have hrp : Function.Periodic r L0 := by
    intro x
    change rhat (v0 * (x + L0)) = rhat (v0 * x)
    rw [mul_add]
    exact hrhatp (v0 * x)
  have hproject : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => ρ (rhat y)) :=
    hρ.comp_contMDiff hrhat.contMDiff (fun y => (hrhatfix y).1)
  refine ⟨r, m, mul_pos hv0 hmhat, hmspeed, hr, hrp,
    fun x => hrhatfix (v0 * x), ?_, ?_, ?_⟩
  · intro x
    change mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (rhat (v0 * x)) (deriv r x) ≠ 0
    erw [hr1, map_smul]
    exact smul_ne_zero hv0.ne' (hrhatimm _)
  · intro x
    calc
      curveSpeed F (fun y _ => ρ (r y)) t x =
          v0 * curveSpeed F (fun y _ => ρ (rhat y)) t (v0 * x) :=
        curveSpeed_comp F (fun y _ => ρ (rhat y))
          (hproject.mdifferentiable (by simp) _) (hlin x) hv0.le
      _ = m := by rw [hrhatspeed]
  · intro x
    change ‖r x - c x‖ < eps ∧ ‖deriv r x - deriv c x‖ < eps ∧
      ‖deriv (deriv r) x - deriv (deriv c) x‖ < eps
    have hn := hnear (v0 * x)
    change ‖rhat (v0 * x) - chat (v0 * x)‖ < delta ∧
      ‖deriv rhat (v0 * x) - deriv chat (v0 * x)‖ < delta ∧
      ‖deriv (deriv rhat) (v0 * x) - deriv (deriv chat) (v0 * x)‖ < delta at hn
    refine ⟨?_, ?_, ?_⟩
    · change ‖rhat (v0 * x) - c x‖ < eps
      rw [hcc]
      exact hn.1.trans hsmall0
    · rw [hr1, hc1, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hv0]
      exact (mul_lt_mul_of_pos_left hn.2.1 hv0).trans hsmall1
    · rw [hr2, hc2, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg v0)]
      exact (mul_lt_mul_of_pos_left hn.2.2 (sq_pos_of_pos hv0)).trans hsmall2

end PoincareConjecture.M63
