import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessSelectedFootpoint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology RealInnerProductSpace

namespace PoincareConjecture.M63

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem selectedCurveLabel_hasDerivAt {r : ℝ → E} (hr : ContDiff ℝ ∞ r)
    {m M B rho eps : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hB : 0 ≤ B) (hrho : 0 < rho) (heps : 0 < eps)
    (hlower : ∀ s, m ≤ ‖deriv r s‖) (hupper : ∀ s, ‖deriv r s‖ ≤ M)
    (hsecond : ∀ s, ‖deriv (deriv r) s‖ ≤ B)
    (hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2)
    (hmargin : 4 * eps * M ≤ m ^ 2 * rho)
    {c : ℝ → E} (hc : ContDiff ℝ 2 c) {eta : ℝ} (heta : 0 ≤ eta)
    (htrans : 2 * M * (eta + B * rho) ≤ m ^ 2)
    (hclose : ∀ x, ‖c x - r x‖ < eps)
    (hfirst : ∀ x, ‖deriv c x - deriv r x‖ ≤ eta) (x : ℝ) :
    let f : ℝ → ℝ := fun s => selectedCurveFootpoint r rho eps (s, c s)
    let y := f x
    HasDerivAt f (⟪deriv c x, deriv r y⟫ /
      (‖deriv r y‖ ^ 2 - ⟪c x - r y, deriv (deriv r) y⟫)) x ∧ 0 < deriv f x := by
  let pi := selectedCurveFootpoint r rho eps
  let f : ℝ → ℝ := fun s => pi (s, c s)
  let y := f x
  let D := ‖deriv r y‖ ^ 2 - ⟪c x - r y, deriv (deriv r) y⟫
  obtain ⟨hpi, hpid⟩ := selectedCurveFootpoint_contDiffAt hr hm hM hB hrho heps
    hlower hupper hsecond hsmall hmargin (x, c x) (hclose x)
  have hpair : HasDerivAt (fun s => (s, c s)) (1, deriv c x) x :=
    (hasDerivAt_id x).prodMk (hc.differentiable (by norm_num) x).hasDerivAt
  have hdf : HasDerivAt f (⟪deriv c x, deriv r y⟫ / D) x := by
    have hd := (hpi.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x hpair
    rw [hpid (1, deriv c x)] at hd
    exact hd
  have hy := (selectedCurveFootpoint_spec hr hm hM hB hrho heps
    hlower hupper hsecond hsmall hmargin).1 (x, c x) (hclose x)
  have hwindow : y ∈ Icc (x - rho) (x + rho) := by
    have habs : |y - x| < rho := hy.1
    exact ⟨by linarith [(abs_lt.mp habs).1], by linarith [(abs_lt.mp habs).2]⟩
  have hD : 0 < D := lt_of_lt_of_le (by positivity)
    (curveFootpoint_denominator_lower hr hm hM hB hrho heps hlower hupper
      hsecond hsmall (hclose x) hwindow)
  have hLip : ‖deriv r y - deriv r x‖ ≤ B * |y - x| := by
    simpa only [Real.norm_eq_abs] using
      (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun s _ => ((contDiff_infty_iff_deriv.mp hr).2.differentiable (by simp) s))
        (fun s _ => hsecond s) (mem_univ x) (mem_univ y)
  have hdist : ‖deriv c x - deriv r y‖ ≤ eta + B * rho := calc
    _ ≤ ‖deriv c x - deriv r x‖ + ‖deriv r x - deriv r y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (deriv c x) (deriv r x) (deriv r y)
    _ = ‖deriv c x - deriv r x‖ + ‖deriv r y - deriv r x‖ := by
      rw [norm_sub_rev (deriv r x) (deriv r y)]
    _ ≤ eta + B * rho := add_le_add (hfirst x)
      (hLip.trans (mul_le_mul_of_nonneg_left (show |y - x| ≤ rho from hy.1.le) hB))
  have hinner : |⟪deriv c x - deriv r y, deriv r y⟫| ≤ (eta + B * rho) * M :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul hdist (hupper y) (norm_nonneg _) (by positivity))
  have hsquare : m ^ 2 ≤ ‖deriv r y‖ ^ 2 := by
    nlinarith [hlower y, norm_nonneg (deriv r y)]
  have hnum : 0 < ⟪deriv c x, deriv r y⟫ := by
    have hlo := (abs_le.mp hinner).1
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hlo
    nlinarith [sq_pos_of_pos hm]
  exact ⟨hdf, hdf.deriv.symm ▸ div_pos hnum hD⟩

theorem exists_curveNormalGraph_orderIso {r : ℝ → E} (hr : ContDiff ℝ ∞ r)
    {m M B rho eps : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hB : 0 ≤ B) (hrho : 0 < rho) (heps : 0 < eps)
    (hlower : ∀ s, m ≤ ‖deriv r s‖) (hupper : ∀ s, ‖deriv r s‖ ≤ M)
    (hsecond : ∀ s, ‖deriv (deriv r) s‖ ≤ B)
    (hsmall : 2 * B * (eps + M * rho) ≤ m ^ 2)
    (hmargin : 4 * eps * M ≤ m ^ 2 * rho)
    {c : ℝ → E} (hc : ContDiff ℝ 2 c) {eta : ℝ} (heta : 0 ≤ eta)
    (htrans : 2 * M * (eta + B * rho) ≤ m ^ 2)
    (hclose : ∀ x, ‖c x - r x‖ < eps)
    (hfirst : ∀ x, ‖deriv c x - deriv r x‖ ≤ eta)
    {P : ℝ} (hP : 0 < P) (hrper : Function.Periodic r P)
    (hcper : Function.Periodic c P) :
    ∃ phi : ℝ ≃o ℝ,
      (∀ x, phi x = selectedCurveFootpoint r rho eps (x, c x)) ∧
      ContDiff ℝ 2 (phi : ℝ → ℝ) ∧ ContDiff ℝ 2 (phi.symm : ℝ → ℝ) ∧
      (∀ x, |phi x - x| < rho) ∧ (∀ x, 0 < deriv phi x) ∧
      (∀ y, HasDerivAt phi.symm ((deriv phi (phi.symm y))⁻¹) y ∧
        0 < deriv phi.symm y) ∧
      (∀ x, phi (x + P) = phi x + P) ∧
      (∀ y, phi.symm (y + P) = phi.symm y + P) ∧
      let U : ℝ → E := fun y => c (phi.symm y) - r y
      ContDiff ℝ 2 U ∧ Function.Periodic U P ∧
      (∀ y, ⟪U y, deriv r y⟫ = 0) ∧ ∀ x, c x = r (phi x) + U (phi x) := by
  let f : ℝ → ℝ := fun x => selectedCurveFootpoint r rho eps (x, c x)
  have hspec := selectedCurveFootpoint_spec hr hm hM hB hrho heps
    hlower hupper hsecond hsmall hmargin
  have hwindow (x : ℝ) : |f x - x| < rho := (hspec.1 (x, c x) (hclose x)).1
  have hf : ContDiff ℝ 2 f := contDiff_iff_contDiffAt.mpr fun x => by
    have hpi := (selectedCurveFootpoint_contDiffAt hr hm hM hB hrho heps
      hlower hupper hsecond hsmall hmargin (x, c x) (hclose x)).1
    exact (hpi.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp x
      (contDiffAt_id.prodMk hc.contDiffAt)
  have hd (x : ℝ) : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by norm_num) x).hasDerivAt
  have hpos (x : ℝ) : 0 < deriv f x :=
    (selectedCurveLabel_hasDerivAt hr hm hM hB hrho heps hlower hupper hsecond hsmall
      hmargin hc heta htrans hclose hfirst x).2
  have hmono : StrictMono f := strictMono_of_hasDerivAt_pos hd hpos
  have hsurj : Function.Surjective f := by
    intro z
    have hl := (abs_lt.mp (hwindow (z - rho - 1))).2
    have hu := (abs_lt.mp (hwindow (z + rho + 1))).1
    obtain ⟨x, _hx, heq⟩ := intermediate_value_Icc
      (show z - rho - 1 ≤ z + rho + 1 by linarith) hf.continuous.continuousOn
      (show z ∈ Icc (f (z - rho - 1)) (f (z + rho + 1)) from
        ⟨by linarith, by linarith⟩)
    exact ⟨x, heq⟩
  let phi : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective f hmono hsurj
  have hinvSmooth : ContDiff ℝ 2 (phi.symm : ℝ → ℝ) :=
    phi.toHomeomorph.contDiff_symm_deriv (fun x => (hpos x).ne') hd hf
  have hinv (y : ℝ) : HasDerivAt phi.symm ((deriv phi (phi.symm y))⁻¹) y :=
    (hd (phi.symm y)).of_local_left_inverse phi.symm.toHomeomorph.continuous.continuousAt
      (hpos _).ne' (Eventually.of_forall phi.apply_symm_apply)
  have hshift (x : ℝ) : phi (x + P) = phi x + P := by
    change selectedCurveFootpoint r rho eps (x + P, c (x + P)) =
      selectedCurveFootpoint r rho eps (x, c x) + P
    rw [hcper x]
    exact hspec.2.2 P hP hrper x (c x)
  have hinvShift (y : ℝ) : phi.symm (y + P) = phi.symm y + P := by
    apply phi.injective
    rw [phi.apply_symm_apply, hshift, phi.apply_symm_apply]
  refine ⟨phi, fun _ => rfl, hf, hinvSmooth, hwindow, hpos, ?_, hshift, hinvShift, ?_⟩
  · intro y
    exact ⟨hinv y, (hinv y).deriv.symm ▸ inv_pos.mpr (hpos (phi.symm y))⟩
  · refine ⟨(hc.comp hinvSmooth).sub
      (hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)), ?_, ?_, ?_⟩
    · intro y
      simp only [hinvShift, hcper (phi.symm y), hrper y]
    · intro y
      have hroot := (hspec.1 (phi.symm y, c (phi.symm y)) (hclose (phi.symm y))).2
      change ⟪c (phi.symm y) - r (phi (phi.symm y)), deriv r (phi (phi.symm y))⟫ = 0 at hroot
      simpa only [phi.apply_symm_apply] using hroot
    · intro x
      change c x = r (phi x) + (c (phi.symm (phi x)) - r (phi x))
      rw [phi.symm_apply_apply]
      abel

end PoincareConjecture.M63
