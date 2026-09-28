import PoincareConjecture.Proofs.M14.Sec6_3_PrefixMinimality
import PoincareConjecture.Proofs.M14.Sec6_2_SquarePathPrefix
import PoincareConjecture.Proofs.M14.Sec6_1_SquareDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

theorem positiveStart_reducedLengthAt_square_prefix
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hp : M14IsMinimizing p)
    (R : M14SquareRootPath G p) {s : ℝ}
    (hs : s ∈ Ioc (Real.sqrt a) (Real.sqrt b)) :
    M14ReducedLengthAt G T a x (R.curve s) =
      (∫ r in Real.sqrt a..s, squareRootLIntegrand R r) / (2 * s) := by
  have hs0 : 0 < s := (Real.sqrt_nonneg a).trans_lt hs.1
  have hsC : s ∈ M14SqrtParameterInterval a b := ⟨hs.1.le, hs.2⟩
  rcases lt_or_eq_of_le hs.2 with hlt | rfl
  · have hac : a < s ^ 2 := by
      nlinarith [Real.sq_sqrt p.tau_nonneg, Real.sqrt_nonneg a, hs.1]
    have hcb : s ^ 2 < b := by
      nlinarith [Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), Real.sqrt_nonneg b]
    have hmin := isMinimizing_prefixPath hM12 p hp (show s ^ 2 ∈ Ioo a b from ⟨hac, hcb⟩)
    have haction := integral_squareRootLIntegrand_eq_action (prefixSquarePath R hac hcb.le)
    change (∫ r in Real.sqrt a..Real.sqrt (s ^ 2), squareRootLIntegrand R r) =
      M14BackwardLAction G (prefixPath p (s ^ 2) hac hcb.le) at haction
    rw [Real.sqrt_sq hs0.le] at haction
    unfold M14ReducedLengthAt
    rw [R.curve_time s hsC, sub_sub_cancel, R.agrees s hsC,
      reducedLengthValue_eq_of_minimizing _ hmin, Real.sqrt_sq hs0.le, haction]
  · have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
    have hpoint : R.curve (Real.sqrt b) = y := by
      rw [R.agrees _ hsC, Real.sq_sqrt hb.le, p.curve_end]
    unfold M14ReducedLengthAt
    rw [R.curve_time _ hsC, Real.sq_sqrt hb.le, sub_sub_cancel, hpoint,
      reducedLengthValue_eq_of_minimizing p hp, integral_squareRootLIntegrand_eq_action R]

theorem positiveStart_reducedLengthAt_square_hasDerivWithinAt
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hp : M14IsMinimizing p)
    (R : M14SquareRootPath G p) :
    HasDerivWithinAt (fun r => M14ReducedLengthAt G T a x (R.curve r))
      ((squareRootLIntegrand R (Real.sqrt b) * (2 * Real.sqrt b) -
        M14BackwardLAction G p * 2) / (2 * Real.sqrt b) ^ 2)
      (M14SqrtParameterInterval a b) (Real.sqrt b) := by
  let C := M14SqrtParameterInterval a b
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hb : 0 < b := p.tau_nonneg.trans_lt p.tau_lt
  have hs : Real.sqrt b ∈ C := ⟨hab.le, le_rfl⟩
  have hcont := (squareRootLIntegrand_contDiffOn hM12 R).continuousOn
  let : Fact (Real.sqrt b ∈ Icc (Real.sqrt a) (Real.sqrt b)) := ⟨hs⟩
  have hderiv := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Icc (Real.sqrt a) (Real.sqrt b)) (t := Icc (Real.sqrt a) (Real.sqrt b))
    (squareRootLIntegrand_intervalIntegrable R)
    (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc (Real.sqrt b))
    (hcont _ hs)
  have hden : HasDerivWithinAt (fun r : ℝ => 2 * r) 2 C (Real.sqrt b) := by
    simpa only [id_eq, mul_one] using (hasDerivWithinAt_id (Real.sqrt b) C).const_mul 2
  have hquot := hderiv.div hden (mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)).ne'
  rw [integral_squareRootLIntegrand_eq_action R] at hquot
  apply hquot.congr_of_eventuallyEq_of_mem _ hs
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)] with r hr hr0
  exact positiveStart_reducedLengthAt_square_prefix hM12 hp R ⟨hr0, hr.2⟩

end PoincareConjecture.M14
