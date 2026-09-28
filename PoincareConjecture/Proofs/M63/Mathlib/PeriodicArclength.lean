import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M63

theorem exists_periodic_arclength_homeomorph {p : ℝ} (hp : 0 < p)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hperiod : Function.Periodic v p)
    (hpos : ∀ x, 0 < v x) :
    let ell := ∫ x in (0 : ℝ)..p, v x
    0 < ell ∧ ∃ phi : ℝ ≃ₜ ℝ,
      (∀ x, phi x = (p / ell) * ∫ y in (0 : ℝ)..x, v y) ∧
      ContDiff ℝ 2 (phi : ℝ → ℝ) ∧ ContDiff ℝ 2 (phi.symm : ℝ → ℝ) ∧
      phi 0 = 0 ∧ (∀ x, phi (x + p) = phi x + p) ∧
      (∀ y, phi.symm (y + p) = phi.symm y + p) ∧
      (∀ x, HasDerivAt phi ((p / ell) * v x) x ∧ 0 < deriv phi x) ∧
      ∀ y, HasDerivAt phi.symm (ell / (p * v (phi.symm y))) y ∧
        0 < deriv phi.symm y := by
  let ell := ∫ x in (0 : ℝ)..p, v x
  have hell : 0 < ell :=
    intervalIntegral.intervalIntegral_pos_of_pos (hv.continuous.intervalIntegrable 0 p) hpos hp
  have hscale : 0 < p / ell := div_pos hp hell
  let f : ℝ → ℝ := fun x => (p / ell) * ∫ y in (0 : ℝ)..x, v y
  have hd (x : ℝ) : HasDerivAt f ((p / ell) * v x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hv.continuous.intervalIntegrable 0 x)
      hv.continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      hv.continuous.continuousAt).const_mul (p / ell)
  have hderiv : deriv f = fun x => (p / ell) * v x := funext fun x => (hd x).deriv
  have hf : ContDiff ℝ 2 f := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
    rw [hderiv]
    exact contDiff_const.mul hv
  have hmono : StrictMono f := strictMono_of_hasDerivAt_pos hd (fun x => mul_pos hscale (hpos x))
  have hsurj : Function.Surjective f := hf.continuous.surjective
    ((hperiod.tendsto_atTop_intervalIntegral_of_pos hell hp).const_mul_atTop hscale)
    ((hperiod.tendsto_atBot_intervalIntegral_of_pos hell hp).const_mul_atBot hscale)
  let phi : ℝ ≃ₜ ℝ := (StrictMono.orderIsoOfSurjective f hmono hsurj).toHomeomorph
  have hphi (x : ℝ) : HasDerivAt phi ((p / ell) * v x) x := hd x
  have hshift (x : ℝ) : phi (x + p) = phi x + p := by
    change (p / ell) * (∫ y in (0 : ℝ)..x + p, v y) =
      (p / ell) * (∫ y in (0 : ℝ)..x, v y) + p
    rw [hperiod.intervalIntegral_add_eq_add 0 x
      (fun s t => hv.continuous.intervalIntegrable s t), zero_add]
    change (p / ell) * ((∫ y in (0 : ℝ)..x, v y) + ell) = _
    field_simp
  have hinv (y : ℝ) : HasDerivAt phi.symm (ell / (p * v (phi.symm y))) y := by
    have h := (hphi (phi.symm y)).of_local_left_inverse phi.symm.continuous.continuousAt
      (mul_pos hscale (hpos _)).ne' (Eventually.of_forall phi.apply_symm_apply)
    convert h using 1 <;> first | rfl | field_simp
  refine ⟨hell, phi, fun _ => rfl, hf,
    phi.contDiff_symm_deriv (fun x => (mul_pos hscale (hpos x)).ne') hphi hf,
    ?_, hshift, ?_, ?_, ?_⟩
  · change (p / ell) * (∫ y in (0 : ℝ)..0, v y) = 0
    simp
  · intro y
    apply phi.injective
    rw [phi.apply_symm_apply, hshift, phi.apply_symm_apply]
  · intro x
    exact ⟨hphi x, (hphi x).deriv.symm ▸ mul_pos hscale (hpos x)⟩
  · intro y
    exact ⟨hinv y, (hinv y).deriv.symm ▸ div_pos hell (mul_pos hp (hpos _))⟩

end PoincareConjecture.M63
