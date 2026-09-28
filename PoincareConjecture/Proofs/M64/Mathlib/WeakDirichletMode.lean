import PoincareConjecture.Proofs.M08.WeakVelocity
import PoincareConjecture.Proofs.M64.Mathlib.DirichletModeUniqueness













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture






theorem m64WeakDerivative_continuous_representative
    {a b : ℝ} (hab : a < b) {u q : ℝ → ℝ}
    (hu : IntegrableOn u (Icc a b) volume) (hq : ContinuousOn q (Icc a b))
    (hweak : ∀ phi : ℝ → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Ioo a b →
      (∫ x in Icc a b, deriv phi x * u x) = -(∫ x in Icc a b, phi x * q x)) :
    ∃ U : ℝ → ℝ, ContinuousOn U (Icc a b) ∧ u =ᵐ[volume.restrict (Icc a b)] U ∧
      ∀ x ∈ Ioo a b, HasDerivAt U (q x) x := by
  have hui := (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hu
  have hqi : IntervalIntegrable q volume a b := hq.intervalIntegrable_of_Icc hab.le
  obtain ⟨c, hc⟩ := M08.weak_momentum_primitive hab u q hui hqi (by
    intro phi hp hc hs
    simpa only [intervalIntegral.integral_of_le hab.le,
      ← integral_Icc_eq_integral_Ioc, smul_eq_mul] using hweak phi hp hc hs)
  let U : ℝ → ℝ := fun x => c + ∫ y in a..x, q y
  have hU : ContinuousOn U (Icc a b) := by
    have hh := intervalIntegral.continuousOn_primitive_interval' hqi left_mem_uIcc
    rw [uIcc_of_le hab.le] at hh
    exact continuousOn_const.add hh
  have hd := (M08.continuous_primitive_regular hab U q hq (by
    intro x _
    simp only [U, intervalIntegral.integral_same, add_zero])).1
  exact ⟨U, hU, hc, fun x hx =>
    (hd x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)⟩






theorem m64Continuous_weak_derivative
    {a b : ℝ} (hab : a < b) {u q : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hweak : ∀ phi : ℝ → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Ioo a b →
      (∫ x in Icc a b, deriv phi x * u x) = -(∫ x in Icc a b, phi x * q x)) :
    ∀ x ∈ Ioo a b, HasDerivAt u (q x) x := by
  obtain ⟨U, hU, heq, hd⟩ := m64WeakDerivative_continuous_representative hab
    (hu.integrableOn_compact isCompact_Icc) hq hweak
  have hp := Measure.eqOn_Icc_of_ae_eq volume hab.ne heq hu hU
  intro x hx
  apply (hd x hx).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact hp (Ioo_subset_Icc_self hy)





theorem m64WeakDirichlet_coupled_zero
    {a b alpha beta : ℝ} (hab : a < b) (hsign : 0 ≤ alpha * beta)
    {u v V : ℝ → ℝ} (hu : IntegrableOn u (Icc a b) volume)
    (hV : ContinuousOn V (Icc a b)) (hv : v =ᵐ[volume.restrict (Icc a b)] V)
    (hVa : V a = 0) (hVb : V b = 0)
    (hfirst : ∀ phi : ℝ → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Ioo a b →
      (∫ x in Icc a b, deriv phi x * v x) =
        -(∫ x in Icc a b, phi x * (alpha * u x)))
    (hsecond : ∀ phi : ℝ → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Ioo a b →
      (∫ x in Icc a b, deriv phi x * u x) =
        -(∫ x in Icc a b, phi x * (beta * v x))) :
    v =ᵐ[volume.restrict (Icc a b)] (fun _ => 0) ∧
      (fun x => alpha * u x) =ᵐ[volume.restrict (Icc a b)] (fun _ => 0) := by
  have hsecond' : ∀ phi : ℝ → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Ioo a b →
      (∫ x in Icc a b, deriv phi x * u x) =
        -(∫ x in Icc a b, phi x * (beta * V x)) := by
    intro phi hp hc hs
    rw [hsecond phi hp hc hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  obtain ⟨U, hU, huU, hdU⟩ := m64WeakDerivative_continuous_representative
    (q := fun x => beta * V x) hab hu
    (continuousOn_const.mul hV) hsecond'
  have hdV : ∀ x ∈ Ioo a b, HasDerivAt V (alpha * U x) x := by
    apply m64Continuous_weak_derivative (q := fun x => alpha * U x) hab hV
      (continuousOn_const.mul hU)
    intro phi hp hc hs
    calc
      _ = ∫ x in Icc a b, deriv phi x * v x := by
        apply integral_congr_ae
        filter_upwards [hv] with x hx
        rw [hx]
      _ = -(∫ x in Icc a b, phi x * (alpha * u x)) := hfirst phi hp hc hs
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [huU] with x hx
        rw [hx]
  have hzero : EqOn V (fun _ => 0) (Icc a b) :=
    m64Dirichlet_nonnegative_potential_eq_zero hV hdV
      (fun x hx => by
        have hd : HasDerivAt (fun y => alpha * U y)
            (0 * U x + alpha * (beta * V x)) x :=
          (hasDerivAt_const x alpha).mul (hdU x hx)
        simpa only [zero_mul, zero_add, mul_assoc] using hd)
      (fun _ _ => hsign) hVa hVb
  have hI : ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  constructor
  · filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with x hx hxI
    exact hx.trans (hzero hxI)
  · filter_upwards [huU, hI] with x hx hxI
    rw [hx]
    have heq : V =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
      exact hzero (Ioo_subset_Icc_self hy)
    exact (hdV x hxI).unique ((hasDerivAt_const x 0).congr_of_eventuallyEq heq)

end PoincareConjecture
