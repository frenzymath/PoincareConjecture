import PoincareConjecture.Proofs.M35.RadialGauge.ForcingContinuity
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingJetAlgebra
import PoincareConjecture.Proofs.M35.RadialGauge.EvenRadialCompactJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

open SmoothRadial

variable {A E : Type*} [TopologicalSpace A] [CompactSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem compact_profile_jets {f : A → ℝ → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (he : ∀ a, Function.Even (f a))
    (hj : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (f p.1) p.2)) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ p : E × ℝ, ‖p.1‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j (fun q : E × ℝ => f a ‖q.1‖) p‖ ≤ C := by
  have hscalar (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, |r| ≤ 1 →
      |iteratedDeriv j (f a) r| ≤ C := by
    have hc : IsCompact ((univ : Set A) ×ˢ Icc (-1 : ℝ) 1) :=
      isCompact_univ.prod isCompact_Icc
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hj j).continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro a r hr
    have hv : |iteratedDeriv j (f a) r| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (a, r) ⟨mem_univ _, abs_le.mp hr⟩
    exact hv.trans (le_max_left _ _)
  intro j
  obtain ⟨C, hC, hCb⟩ :=
    even_radial_compact_jets_bounded (E := E) zero_le_one hf he hscalar j
  refine ⟨C, hC, ?_⟩
  intro a p hp
  have hl := norm_jet_comp_linear_le (ContinuousLinearMap.fst ℝ E ℝ)
    (ContinuousLinearMap.norm_fst_le ℝ E ℝ) isOpen_univ
    (contDiff_even_norm (hf a) (he a)).contDiffOn (mem_univ p.1) j
  exact hl.trans (hCb a p.1 hp)

theorem smoothGaugeForcing_compact_jets
    {h xi : A → ℝ → ℝ} {f₀ : ℝ → ℝ} {eta : ℝ}
    (hh : ∀ a, ContDiff ℝ ∞ (h a)) (he : ∀ a, Function.Even (h a))
    (hxi : ∀ a, ContDiff ℝ ∞ (xi a)) (hxie : ∀ a, Function.Even (xi a))
    (hf : ContDiff ℝ ∞ f₀) (hfo : Function.Odd f₀)
    (hhj : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (h p.1) p.2))
    (hxij : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (xi p.1) p.2)) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ∀ x : E, ∀ sigma,
      ‖x‖ ≤ 1 → |sigma| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : E × ℝ => smoothGaugeForcing (h a) f₀ (xi a)
        p.1 p.2) (x, sigma)‖ ≤ C := by
  let D (a : A) := axisDivision (deriv (h a))
  let e (a : A) (r : ℝ) := Real.exp (-2 * h a r)
  let Q (a : A) := smoothEvenQuadratic (e a)
  let S := Metric.closedBall (0 : E) 1 ×ˢ Icc (-eta) eta
  have hS : S ⊆ (univ : Set (E × ℝ)) := subset_univ _
  have hDs (a : A) : ContDiff ℝ ∞ (D a) :=
    axisDivision_contDiff (contDiff_infty_iff_deriv.mp (hh a)).2
  have hDe (a : A) : Function.Even (D a) := axisDivision_deriv_even (hh a) (he a)
  have hDj (j : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv j (D p.1) p.2) := by
    apply axisDivision_jet_continuous (fun a => (contDiff_infty_iff_deriv.mp (hh a)).2) j
    simpa only [iteratedDeriv_succ'] using hhj (j + 2)
  have hes (a : A) : ContDiff ℝ ∞ (e a) := (contDiff_const.mul (hh a)).exp
  have hee (a : A) : Function.Even (e a) :=
    fun r => congrArg (fun z => Real.exp (-2 * z)) (he a r)
  have hej (j : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv j (e p.1) p.2) := by
    apply scalar_jets_continuous_exp (fun a => contDiff_const.mul (hh a))
    intro i
    simpa only [iteratedDeriv_const_mul_field] using (hhj i).const_mul (-2)
  have hQs (a : A) : ContDiff ℝ ∞ (Q a) :=
    smoothEvenQuadratic_contDiff (hes a)
  have hQe (a : A) : Function.Even (Q a) := smoothEvenQuadratic_even (hes a) (hee a)
  have hQj (j : ℕ) : Continuous (fun p : A × ℝ => iteratedDeriv j (Q p.1) p.2) := by
    exact axisDivision_jet_continuous (fun a => axisDivision_contDiff (hes a)) j
      (axisDivision_jet_continuous hes (j + 1) (hej (j + 2)))
  have hprofile {f : A → ℝ → ℝ}
      (hs : ∀ a, ContDiff ℝ ∞ (f a)) (hp : ∀ a, Function.Even (f a))
      (hc : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (f p.1) p.2)) :
      ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a p, p ∈ S →
        ‖iteratedFDeriv ℝ j (fun q : E × ℝ => f a ‖q.1‖) p‖ ≤ C := by
    intro j
    obtain ⟨C, hC, hCb⟩ := compact_profile_jets (E := E) hs hp hc j
    exact ⟨C, hC, fun a p hp => hCb a p (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1)⟩
  let target (p : E × ℝ) :=
    2 * Real.exp (2 * p.2) * targetQuadraticRemainder f₀ ‖Real.exp p.2 • p.1‖
  have htarget : ContDiff ℝ ∞ target := by
    have hrad := contDiff_even_norm (E := E) (targetQuadraticRemainder_contDiff hf)
      (targetQuadraticRemainder_even hf hfo)
    exact (contDiff_const.mul (contDiff_const.mul contDiff_snd).exp).mul
      (hrad.comp (contDiff_snd.exp.smul contDiff_fst))
  have htargetb (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (_a : A) p, p ∈ S →
      ‖iteratedFDeriv ℝ j target p‖ ≤ C := by
    have hc : IsCompact S := (isCompact_closedBall (0 : E) 1).prod isCompact_Icc
    obtain ⟨C, hCb⟩ := hc.exists_bound_of_continuousOn
      (htarget.continuous_iteratedFDeriv
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun _ p hp => (hCb p hp).trans (le_max_left _ _)⟩
  have hradial {f : A → ℝ → ℝ} (hs : ∀ a, ContDiff ℝ ∞ (f a))
      (hp : ∀ a, Function.Even (f a)) (a : A) :
      ContDiffOn ℝ ∞ (fun p : E × ℝ => f a ‖p.1‖) univ :=
    ((contDiff_even_norm (hs a) (hp a)).comp contDiff_fst).contDiffOn
  have hDb := family_jet_bounds_const_mul isOpen_univ hS (hradial hDs hDe)
    (hprofile hDs hDe hDj) 2
  have hQb := family_jet_bounds_const_mul isOpen_univ hS (hradial hQs hQe)
    (hprofile hQs hQe hQj) 2
  have hfirst := family_jet_bounds_sub isOpen_univ hS
    (fun a => contDiffOn_const.mul (hradial hDs hDe a))
    (fun a => contDiffOn_const.mul (hradial hQs hQe a)) hDb hQb
  have hprod := family_jet_bounds_mul isOpen_univ hS (fun _ => htarget.contDiffOn)
    (hradial hes hee) htargetb (hprofile hes hee hej)
  have hsecond := family_jet_bounds_sub isOpen_univ hS
    (fun a => (contDiffOn_const.mul (hradial hDs hDe a)).sub
      (contDiffOn_const.mul (hradial hQs hQe a)))
    (fun a => htarget.contDiffOn.mul (hradial hes hee a)) hfirst hprod
  have hfull := family_jet_bounds_sub isOpen_univ hS
    (fun a => ((contDiffOn_const.mul (hradial hDs hDe a)).sub
      (contDiffOn_const.mul (hradial hQs hQe a))).sub
        (htarget.contDiffOn.mul (hradial hes hee a)))
    (hradial hxi hxie) hsecond (hprofile hxi hxie hxij)
  intro j
  obtain ⟨C, hC, hCb⟩ := hfull j
  refine ⟨C, hC, fun a x sigma hx hsigma => ?_⟩
  exact hCb a (x, sigma) ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hx,
    abs_le.mp hsigma⟩

end PoincareConjecture.M35.RadialGauge
