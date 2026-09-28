import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CirclePhaseDerivative
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Def19_12_PositiveDegree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private theorem lift_continuous (sigma : M64PeriodicDegreeOneLift) : Continuous sigma.map := by
  have hLip : LipschitzWith
      (NNReal.mk sigma.lipschitz_constant sigma.lipschitz_nonnegative) sigma.map := by
    intro x y
    have hE := ENNReal.ofReal_le_ofReal (sigma.lipschitz_on x y)
    rw [ENNReal.ofReal_mul sigma.lipschitz_nonnegative] at hE
    simpa only [edist_dist, Real.dist_eq, ENNReal.coe_nnreal_eq, NNReal.coe_mk] using hE
  exact hLip.continuous

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64AnnulusCircleCurrent_sign_of_free_positive_degree_boundary
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {gamma : ℝ → P.charts.Point} (lift : M63PositiveDegreeLift P gamma)
    (sigma : M64PeriodicDegreeOneLift)
    {f : LoopPlane → P.charts.Point} {s : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ f (annulusPoint x s))
    (hboundary : ∀ x, f (annulusPoint x s) = gamma (sigma.map x)) :
    (∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ m64AnnulusCircleCurrent P t f 0 (annulusPoint x s)) ∧
    ∃ x ∈ Ioo (0 : ℝ) curvePeriod,
      0 < m64AnnulusCircleCurrent P t f 0 (annulusPoint x s) := by
  let L := lift.lift ∘ sigma.map
  have hL : Continuous L := lift.regular.continuous.comp (lift_continuous sigma)
  have hmono : Monotone L :=
    (strictMono_of_deriv_pos lift.derivative_positive).monotone.comp sigma.monotone
  have hquot (x : ℝ) : P.circle.quotient (L x) = (f (annulusPoint x s)).2 := by
    rw [hboundary]
    exact lift.quotient_eq (sigma.map x)
  have hderiv (x : ℝ) (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
      m64AnnulusCircleCurrent P t f 0 (annulusPoint x s) = deriv L x :=
    m64AnnulusCircleCurrent_eq_phase_deriv P t (hf x hx) hL.continuousAt hquot
  refine ⟨fun x hx => (hderiv x hx).symm ▸ hmono.deriv_nonneg, ?_⟩
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hdiff : DifferentiableOn ℝ L (Ioo (0 : ℝ) curvePeriod) := by
    intro x hx
    exact (m64Annulus_phase_contDiffAt P (hf x (Ioo_subset_Icc_self hx))
      hL.continuousAt hquot).differentiableAt (by simp) |>.differentiableWithinAt
  obtain ⟨x, hx, hmean⟩ := exists_deriv_eq_slope L hP hL.continuousOn hdiff
  have hincrement : L curvePeriod - L 0 = (lift.degree : ℝ) * circumference := by
    have hs := sigma.period_shift 0
    simp only [zero_add] at hs
    dsimp only [L, Function.comp_apply]
    rw [hs, lift.period_shift]
    ring
  refine ⟨x, hx, ?_⟩
  rw [hderiv x (Ioo_subset_Icc_self hx), hmean, hincrement, sub_zero]
  exact div_pos (mul_pos (by exact_mod_cast lift.degree_positive) P.circle.positive) hP

theorem m64AnnulusCircleCurrent_sign_of_free_ramp_boundary
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {gamma : ℝ → P.charts.Point}
    (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hramp : M63IsRampAt P gamma t) (sigma : M64PeriodicDegreeOneLift)
    {f : LoopPlane → P.charts.Point} {s : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ f (annulusPoint x s))
    (hboundary : ∀ x, f (annulusPoint x s) = gamma (sigma.map x)) :
    (∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ m64AnnulusCircleCurrent P t f 0 (annulusPoint x s)) ∧
    ∃ x ∈ Ioo (0 : ℝ) curvePeriod,
      0 < m64AnnulusCircleCurrent P t f 0 (annulusPoint x s) := by
  obtain ⟨lift⟩ := m63PositiveDegreeLift_nonempty P gamma hperiod hgamma hramp
  exact m64AnnulusCircleCurrent_sign_of_free_positive_degree_boundary P t lift sigma hf hboundary

end PoincareConjecture
