import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessFootpointQuantitative
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Mul









set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology RealInnerProductSpace

namespace PoincareConjecture.M63

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]




noncomputable def selectedCurveFootpoint (r : ℝ → E) (rho eps : ℝ)
    (p : ℝ × E) : ℝ := by
  classical
  exact if h : ‖p.2 - r p.1‖ < eps ∧
      ∃ y, |y - p.1| < rho ∧ curveFootpointResidual r (p.2, y) = 0
  then Classical.choose h.2 else p.1




theorem selectedCurveFootpoint_spec {r : ℝ → E} (hr : ContDiff ℝ ∞ r)
    {m M B rho eps : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hB : 0 ≤ B) (hrho : 0 < rho) (heps : 0 < eps)
    (hlower : ∀ s, m ≤ ‖deriv r s‖) (hupper : ∀ s, ‖deriv r s‖ ≤ M)
    (hsecond : ∀ s, ‖deriv (deriv r) s‖ ≤ B)
    (hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2)
    (hmargin : 4 * eps * M ≤ m ^ 2 * rho) :
    (∀ p : ℝ × E, ‖p.2 - r p.1‖ < eps →
      |selectedCurveFootpoint r rho eps p - p.1| < rho ∧
        curveFootpointResidual r (p.2, selectedCurveFootpoint r rho eps p) = 0) ∧
    (∀ x, selectedCurveFootpoint r rho eps (x, r x) = x) ∧
    (∀ P : ℝ, 0 < P → Function.Periodic r P → ∀ x z,
      selectedCurveFootpoint r rho eps (x + P, z) =
        selectedCurveFootpoint r rho eps (x, z) + P) := by
  classical
  have hroot (p : ℝ × E) (hp : ‖p.2 - r p.1‖ < eps) :
      |selectedCurveFootpoint r rho eps p - p.1| < rho ∧
        curveFootpointResidual r (p.2, selectedCurveFootpoint r rho eps p) = 0 := by
    have hunique := existsUnique_curveFootpoint_near hr hm hM hB hrho heps
      hlower hupper hsecond hsmall hmargin hp
    have hex := hunique.exists
    rw [selectedCurveFootpoint, dif_pos ⟨hp, hex⟩]
    exact Classical.choose_spec hex
  refine ⟨hroot, ?_, ?_⟩
  · intro x
    have hp : ‖r x - r x‖ < eps := by simpa using heps
    have hunique := existsUnique_curveFootpoint_near hr hm hM hB hrho heps
      hlower hupper hsecond hsmall hmargin hp
    exact hunique.unique (hroot (x, r x) hp)
      ⟨by simpa using hrho, by simp [curveFootpointResidual]⟩
  · intro P _hP hperiod x z
    have hderiv_period (y : ℝ) : deriv r (y + P) = deriv r y := by
      have hshift := ((hr.differentiable (by simp) (y + P)).hasDerivAt).comp_add_const y P
      have hshift' : HasDerivAt r (deriv r (y + P)) y := by
        exact hshift.congr_of_eventuallyEq (Eventually.of_forall fun s => (hperiod s).symm)
      exact hshift'.unique (hr.differentiable (by simp) y).hasDerivAt
    have hresidual (y : ℝ) :
        curveFootpointResidual r (z, y + P) = curveFootpointResidual r (z, y) := by
      simp only [curveFootpointResidual, hperiod y, hderiv_period]
    by_cases hp : ‖z - r x‖ < eps
    · have htranslated : ‖z - r (x + P)‖ < eps := by simpa only [hperiod x] using hp
      have hunique := existsUnique_curveFootpoint_near hr hm hM hB hrho heps
        hlower hupper hsecond hsmall hmargin htranslated
      apply hunique.unique (hroot (x + P, z) htranslated)
      refine ⟨?_, ?_⟩
      · simpa only [add_sub_add_right_eq_sub] using (hroot (x, z) hp).1
      · rw [hresidual]
        exact (hroot (x, z) hp).2
    · have htranslated : ¬‖z - r (x + P)‖ < eps := by simpa only [hperiod x] using hp
      simp only [selectedCurveFootpoint, hp, htranslated, false_and, dite_false]





theorem selectedCurveFootpoint_contDiffAt [CompleteSpace E]
    {r : ℝ → E} (hr : ContDiff ℝ ∞ r) {m M B rho eps : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hB : 0 ≤ B) (hrho : 0 < rho) (heps : 0 < eps)
    (hlower : ∀ s, m ≤ ‖deriv r s‖) (hupper : ∀ s, ‖deriv r s‖ ≤ M)
    (hsecond : ∀ s, ‖deriv (deriv r) s‖ ≤ B)
    (hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2)
    (hmargin : 4 * eps * M ≤ m ^ 2 * rho)
    (p : ℝ × E) (hp : ‖p.2 - r p.1‖ < eps) :
    ContDiffAt ℝ ∞ (selectedCurveFootpoint r rho eps) p ∧
    ∀ v : ℝ × E, fderiv ℝ (selectedCurveFootpoint r rho eps) p v =
      ⟪v.2, deriv r (selectedCurveFootpoint r rho eps p)⟫ /
        (‖deriv r (selectedCurveFootpoint r rho eps p)‖ ^ 2 -
          ⟪p.2 - r (selectedCurveFootpoint r rho eps p),
            deriv (deriv r) (selectedCurveFootpoint r rho eps p)⟫) := by
  let pi := selectedCurveFootpoint r rho eps
  let y := pi p
  let D := ‖deriv r y‖ ^ 2 - ⟪p.2 - r y, deriv (deriv r) y⟫
  have hspec := (selectedCurveFootpoint_spec hr hm hM hB hrho heps
    hlower hupper hsecond hsmall hmargin).1
  have hy := hspec p hp
  have hwindow : y ∈ Icc (p.1 - rho) (p.1 + rho) := by
    have habs := abs_lt.mp hy.1
    exact ⟨by dsimp [y, pi]; linarith [habs.1], by dsimp [y, pi]; linarith [habs.2]⟩
  have hDlower : m ^ 2 / 2 ≤ D := curveFootpoint_denominator_lower hr hm hM hB
    hrho heps hlower hupper hsecond hsmall hp hwindow
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hDlower
  have hH := (curveFootpointResidual_contDiff hr).contDiffAt (x := (p.2, y))
  have hc : -D ≠ 0 := neg_ne_zero.mpr hD.ne'
  have hinv : ((fderiv ℝ (curveFootpointResidual r) (p.2, y)).comp
      (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [curveFootpointResidual_partial_at hr]
    have hscalar : -‖deriv r y‖ ^ 2 + ⟪p.2 - r y, deriv (deriv r) y⟫ = -D := by
      dsimp [D]
      ring
    rw [hscalar]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (-D)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext
      intro s
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]
    · apply ContinuousLinearMap.ext
      intro s
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let q := hH.implicitFunction (by simp) hinv
  have hqcenter : q p.2 = y := hH.implicitFunction_apply_self (by simp) hinv
  have hqsmooth : ContDiffAt ℝ ∞ q p.2 := hH.contDiffAt_implicitFunction (by simp) hinv
  have hH0 : curveFootpointResidual r (p.2, y) = 0 := hy.2
  have hqzero : ∀ᶠ z in 𝓝 p.2, curveFootpointResidual r (z, q z) = 0 := by
    simpa only [hH0] using hH.eventually_apply_implicitFunction (by simp) hinv
  have hdom : ∀ᶠ p' : ℝ × E in 𝓝 p, ‖p'.2 - r p'.1‖ < eps :=
    (continuousAt_snd.sub (hr.continuous.continuousAt.comp continuousAt_fst)).norm.eventually_lt
      continuousAt_const hp
  have hqwindow : ∀ᶠ p' : ℝ × E in 𝓝 p, |q p'.2 - p'.1| < rho :=
    ((hqsmooth.continuousAt.comp continuousAt_snd).sub continuousAt_fst).abs.eventually_lt
      continuousAt_const (by change |q p.2 - p.1| < rho; rw [hqcenter]; exact hy.1)
  have hagree : pi =ᶠ[𝓝 p] fun p' => q p'.2 := by
    filter_upwards [hdom, hqwindow, continuousAt_snd.eventually hqzero] with p' hp' hw hz
    exact (existsUnique_curveFootpoint_near hr hm hM hB hrho heps hlower hupper
      hsecond hsmall hmargin hp').unique (hspec p' hp') ⟨hw, hz⟩
  have hpis : ContDiffAt ℝ ∞ pi p :=
    (hqsmooth.comp p contDiffAt_snd).congr_of_eventuallyEq hagree
  refine ⟨hpis, ?_⟩
  intro v
  let l : ℝ → ℝ × E := fun s => p + s • v
  let d := fderiv ℝ pi p v
  have hl : HasDerivAt l v 0 := by
    simpa only [l, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hpi_line : HasDerivAt (fun s => pi (l s)) d 0 := by
    have hf := (hpis.differentiableAt (by simp)).hasFDerivAt
    have hf' : HasFDerivAt pi (fderiv ℝ pi p) (l 0) := by
      simpa only [l, zero_smul, add_zero] using hf
    exact hf'.comp_hasDerivAt 0 hl
  have hz_line : HasDerivAt (fun s => (l s).2) v.2 0 := by
    change HasDerivAt (fun s => p.2 + s • v.2) v.2 0
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v.2).const_add p.2
  have hr₁ := (contDiff_infty_iff_deriv.mp hr).1
  have hr₂ := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hr).2).1
  have hr_line : HasDerivAt (fun s => r (pi (l s))) (d • deriv r y) 0 := by
    have hf : HasDerivAt r (deriv r y) (pi (l 0)) := by
      simpa only [l, zero_smul, add_zero] using (hr₁ y).hasDerivAt
    exact hf.scomp (𝕜 := ℝ) 0 hpi_line
  have hr₂_line : HasDerivAt (fun s => deriv r (pi (l s))) (d • deriv (deriv r) y) 0 := by
    have hf : HasDerivAt (deriv r) (deriv (deriv r) y) (pi (l 0)) := by
      simpa only [l, zero_smul, add_zero] using (hr₂ y).hasDerivAt
    exact hf.scomp (𝕜 := ℝ) 0 hpi_line
  have hres : HasDerivAt (fun s => curveFootpointResidual r ((l s).2, pi (l s)))
      (⟪v.2 - d • deriv r y, deriv r y⟫ +
        ⟪p.2 - r y, d • deriv (deriv r) y⟫) 0 := by
    simpa only [curveFootpointResidual, Pi.sub_apply, l, zero_smul, add_zero, add_comm] using
      (hz_line.sub hr_line).inner ℝ hr₂_line
  have hldom : ∀ᶠ s in 𝓝 (0 : ℝ), ‖(l s).2 - r (l s).1‖ < eps := by
    have hlim : Tendsto l (𝓝 0) (𝓝 p) := by
      have hcenter : l 0 = p := by simp only [l, zero_smul, add_zero]
      exact hcenter ▸ hl.continuousAt.tendsto
    exact hlim.eventually hdom
  have hzero : (fun s => curveFootpointResidual r ((l s).2, pi (l s))) =ᶠ[𝓝 0]
      fun _ => (0 : ℝ) := by
    filter_upwards [hldom] with s hs
    exact (hspec (l s) hs).2
  have heq := hres.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero)
  have halgebra : ⟪v.2 - d • deriv r y, deriv r y⟫ +
      ⟪p.2 - r y, d • deriv (deriv r) y⟫ = ⟪v.2, deriv r y⟫ - d * D := by
    dsimp [D]
    simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  change d = ⟪v.2, deriv r y⟫ / D
  apply (eq_div_iff hD.ne').2
  rw [halgebra] at heq
  linarith

end PoincareConjecture.M63
