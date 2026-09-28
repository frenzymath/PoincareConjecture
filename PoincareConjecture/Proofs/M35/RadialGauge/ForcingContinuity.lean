import PoincareConjecture.Proofs.M35.RadialGauge.SmoothGaugeCoefficients
import PoincareConjecture.Proofs.M35.RadialGauge.AxisDivisionJets
import PoincareConjecture.Proofs.M35.RadialGauge.ScalarJetContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial

theorem smoothGaugeForcing_parametric_continuous
    {A E : Type*} [TopologicalSpace A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h xi : A → ℝ → ℝ} {f₀ : ℝ → ℝ}
    (hh : ∀ a, ContDiff ℝ ∞ (h a)) (hf : ContDiff ℝ ∞ f₀)
    (hj : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (h p.1) p.2))
    (hxi : Continuous (fun p : A × ℝ => xi p.1 p.2)) :
    Continuous (fun p : (A × E) × ℝ => smoothGaugeForcing (h p.1.1) f₀ (xi p.1.1) p.1.2 p.2) := by
  let e (a : A) (r : ℝ) := Real.exp (-2 * h a r)
  have hes (a : A) : ContDiff ℝ ∞ (e a) := (contDiff_const.mul (hh a)).exp
  have hec (j : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv j (e p.1) p.2) := by
    apply scalar_jets_continuous_exp (fun a => contDiff_const.mul (hh a))
    intro i
    simpa only [iteratedDeriv_const_mul_field] using (hj i).const_mul (-2)
  have hD : Continuous (fun p : A × ℝ => axisDivision (deriv (h p.1)) p.2) := by
    have hd := axisDivision_jet_continuous
      (fun a => (contDiff_infty_iff_deriv.mp (hh a)).2) 0
      (by simpa only [iteratedDeriv_succ'] using hj 2)
    simpa only [iteratedDeriv_zero] using hd
  have hE : Continuous (fun p : A × ℝ => smoothEvenQuadratic (e p.1) p.2) := by
    have hd1 := axisDivision_jet_continuous hes 1 (hec 2)
    have hd0 := axisDivision_jet_continuous (fun a => axisDivision_contDiff (hes a)) 0 hd1
    simpa only [iteratedDeriv_zero, smoothEvenQuadratic] using hd0
  have harg : Continuous (fun p : (A × E) × ℝ => (p.1.1, ‖p.1.2‖)) :=
    continuous_fst.fst.prodMk continuous_fst.snd.norm
  have hD' := hD.comp harg
  have hE' := hE.comp harg
  have hcurrent := (hec 0).comp harg
  have hxi' := hxi.comp harg
  have hscaled : Continuous (fun p : (A × E) × ℝ =>
      targetQuadraticRemainder f₀ ‖Real.exp p.2 • p.1.2‖) :=
    (targetQuadraticRemainder_contDiff hf).continuous.comp
      (continuous_snd.rexp.smul continuous_fst.snd).norm
  have hfactor : Continuous (fun p : (A × E) × ℝ => Real.exp (2 * p.2)) :=
    (continuous_snd.const_mul 2).rexp
  exact (((hD'.const_mul 2).sub (hE'.const_mul 2)).sub
    (((hfactor.const_mul 2).mul hscaled).mul hcurrent)).sub hxi'

end PoincareConjecture.M35.RadialGauge
