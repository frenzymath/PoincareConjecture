import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessNormalGraph
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousOrderIsoInverse










set_option autoImplicit false

open Set
open scoped ContDiff RealInnerProductSpace

namespace PoincareConjecture.M63

variable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [TopologicalSpace Z]





theorem exists_curveNormalGraph_continuous_family
    {r : ℝ → E} (hr : ContDiff ℝ ∞ r) {m M B rho eps : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hB : 0 ≤ B) (hrho : 0 < rho) (heps : 0 < eps)
    (hlower : ∀ s, m ≤ ‖deriv r s‖) (hupper : ∀ s, ‖deriv r s‖ ≤ M)
    (hsecond : ∀ s, ‖deriv (deriv r) s‖ ≤ B)
    (hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2)
    (hmargin : 4 * eps * M ≤ m ^ 2 * rho)
    {eta : ℝ} (heta : 0 ≤ eta) (htrans : 2 * M * (eta + B * rho) ≤ m ^ 2)
    {P : ℝ} (hP : 0 < P) (hrper : Function.Periodic r P)
    {q : Z → ℝ → E} (hq : Continuous (fun p : Z × ℝ => q p.1 p.2))
    (hq₁ : Continuous (fun p : Z × ℝ => deriv (q p.1) p.2))
    (hqC2 : ∀ z, ContDiff ℝ 2 (q z))
    (hqper : ∀ z, Function.Periodic (q z) P)
    (hclose : ∀ z x, ‖q z x - r x‖ < eps)
    (hfirst : ∀ z x, ‖deriv (q z) x - deriv r x‖ ≤ eta) :
    ∃ phi : Z → (ℝ ≃o ℝ),
      (∀ z,
        (∀ x, phi z x = selectedCurveFootpoint r rho eps (x, q z x)) ∧
        ContDiff ℝ 2 (phi z : ℝ → ℝ) ∧ ContDiff ℝ 2 ((phi z).symm : ℝ → ℝ) ∧
        (∀ x, |phi z x - x| < rho) ∧ (∀ x, 0 < deriv (phi z) x) ∧
        (∀ y, HasDerivAt (phi z).symm ((deriv (phi z) ((phi z).symm y))⁻¹) y ∧
          0 < deriv (phi z).symm y) ∧
        (∀ x, phi z (x + P) = phi z x + P) ∧
        (∀ y, (phi z).symm (y + P) = (phi z).symm y + P) ∧
        let U : ℝ → E := fun y => q z ((phi z).symm y) - r y
        ContDiff ℝ 2 U ∧ Function.Periodic U P ∧
        (∀ y, ⟪U y, deriv r y⟫ = 0) ∧ ∀ x, q z x = r (phi z x) + U (phi z x)) ∧
      Continuous (fun p : Z × ℝ => phi p.1 p.2) ∧
      Continuous (fun p : Z × ℝ => (phi p.1).symm p.2) ∧
      Continuous (fun p : Z × ℝ => deriv (phi p.1) p.2) ∧
      Continuous (fun p : Z × ℝ => deriv (phi p.1).symm p.2) ∧
      Continuous (fun p : Z × ℝ => q p.1 ((phi p.1).symm p.2) - r p.2) ∧
      Continuous (fun p : Z × ℝ =>
        deriv (fun y => q p.1 ((phi p.1).symm y) - r y) p.2) := by
  classical
  have hspatial (z : Z) := exists_curveNormalGraph_orderIso hr hm hM hB hrho heps
    hlower hupper hsecond hsmall hmargin (hqC2 z) heta htrans
      (hclose z) (hfirst z) hP hrper (hqper z)
  choose phi hdata using hspatial
  have hselected (z : Z) (x : ℝ) :
      phi z x = selectedCurveFootpoint r rho eps (x, q z x) := (hdata z).1 x
  have hpos (z : Z) (x : ℝ) : 0 < deriv (phi z) x := (hdata z).2.2.2.2.1 x
  have hinv (z : Z) (y : ℝ) :
      HasDerivAt (phi z).symm ((deriv (phi z) ((phi z).symm y))⁻¹) y ∧
        0 < deriv (phi z).symm y := (hdata z).2.2.2.2.2.1 y
  have hr₁ : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
  have hr₂ : ContDiff ℝ ∞ (deriv (deriv r)) := (contDiff_infty_iff_deriv.mp hr₁).2
  have hPhi : Continuous (fun p : Z × ℝ => phi p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hpi := (selectedCurveFootpoint_contDiffAt hr hm hM hB hrho heps
      hlower hupper hsecond hsmall hmargin (p.2, q p.1 p.2) (hclose p.1 p.2)).1
    have hpair : Continuous (fun p : Z × ℝ => (p.2, q p.1 p.2)) :=
      continuous_snd.prodMk hq
    simpa only [hselected, Function.comp_def] using hpi.continuousAt.comp
      (f := fun p : Z × ℝ => (p.2, q p.1 p.2)) hpair.continuousAt
  have hPsi : Continuous (fun p : Z × ℝ => (phi p.1).symm p.2) :=
    continuous_inverse_orderIso_family phi
      (fun x => hPhi.comp (continuous_id.prodMk continuous_const))
  let D : Z × ℝ → ℝ := fun p => ‖deriv r (phi p.1 p.2)‖ ^ 2 -
    ⟪q p.1 p.2 - r (phi p.1 p.2), deriv (deriv r) (phi p.1 p.2)⟫
  have hD : Continuous D :=
    ((hr₁.continuous.comp hPhi).norm.pow 2).sub
      ((hq.sub (hr.continuous.comp hPhi)).inner (hr₂.continuous.comp hPhi))
  have hDpos (p : Z × ℝ) : 0 < D p := by
    have hw : |phi p.1 p.2 - p.2| < rho := (hdata p.1).2.2.2.1 p.2
    have hwindow : phi p.1 p.2 ∈ Icc (p.2 - rho) (p.2 + rho) :=
      ⟨by linarith [(abs_lt.mp hw).1], by linarith [(abs_lt.mp hw).2]⟩
    exact lt_of_lt_of_le (by positivity)
      (curveFootpoint_denominator_lower hr hm hM hB hrho heps hlower hupper
        hsecond hsmall (hclose p.1 p.2) hwindow)
  have hderiv (z : Z) (x : ℝ) : deriv (phi z) x =
      ⟪deriv (q z) x, deriv r (phi z x)⟫ / D (z, x) := by
    have hd := (selectedCurveLabel_hasDerivAt hr hm hM hB hrho heps
      hlower hupper hsecond hsmall hmargin (hqC2 z) heta htrans
        (hclose z) (hfirst z) x).1
    have heq : (phi z : ℝ → ℝ) = fun y => selectedCurveFootpoint r rho eps (y, q z y) :=
      funext (hselected z)
    simpa only [D, heq] using hd.deriv
  have hPhi₁ : Continuous (fun p : Z × ℝ => deriv (phi p.1) p.2) := by
    have hquot := (hq₁.inner (hr₁.continuous.comp hPhi)).div hD (fun p => (hDpos p).ne')
    exact hquot.congr (fun p => (hderiv p.1 p.2).symm)
  have hPsi₁ : Continuous (fun p : Z × ℝ => deriv (phi p.1).symm p.2) := by
    have hrecip : Continuous (fun p : Z × ℝ =>
        (deriv (phi p.1) ((phi p.1).symm p.2))⁻¹) :=
      (hPhi₁.comp (continuous_fst.prodMk hPsi)).inv₀
        (fun p => (hpos p.1 ((phi p.1).symm p.2)).ne')
    exact hrecip.congr (fun p => (hinv p.1 p.2).1.deriv.symm)
  have hU : Continuous (fun p : Z × ℝ => q p.1 ((phi p.1).symm p.2) - r p.2) :=
    (hq.comp (continuous_fst.prodMk hPsi)).sub (hr.continuous.comp continuous_snd)
  have hU₁ : Continuous (fun p : Z × ℝ =>
      deriv (fun y => q p.1 ((phi p.1).symm y) - r y) p.2) := by
    have hformula (z : Z) (y : ℝ) :
        deriv (fun x => q z ((phi z).symm x) - r x) y =
          deriv (phi z).symm y • deriv (q z) ((phi z).symm y) - deriv r y := by
      have hi := ((hdata z).2.2.1.differentiable (by norm_num) y).hasDerivAt
      have hq' := ((hqC2 z).differentiable (by norm_num) ((phi z).symm y)).hasDerivAt
      exact ((hq'.scomp (𝕜 := ℝ) y hi).sub (hr.differentiable (by simp) y).hasDerivAt).deriv
    exact ((hPsi₁.smul (hq₁.comp (continuous_fst.prodMk hPsi))).sub
      (hr₁.continuous.comp continuous_snd)).congr (fun p => (hformula p.1 p.2).symm)
  exact ⟨phi, hdata, hPhi, hPsi, hPhi₁, hPsi₁, hU, hU₁⟩

end PoincareConjecture.M63
