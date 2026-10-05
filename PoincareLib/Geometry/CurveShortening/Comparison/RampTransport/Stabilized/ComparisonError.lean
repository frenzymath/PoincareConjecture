import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Trimmed.Comparison
import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Stabilized.TrimmedBoundaries

/-! The comparison estimate with the actual approximation error retained.
Source: MT Lemma 19.31, pp. 464-466; trimmed-intrinsic-transport derivation,
Section 13. The actual minimum's boundary regularity is explicit here. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareMT.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}
  {P : M62.CircleProductData F circumference}
  {Q : M62.CircleProductData P.flow auxiliary} {time : ℝ}
  {gamma0 gamma1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric time) gamma0 gamma1} {r epsilon : ℝ}

omit [CompactSpace M] in
/-- The attained minimum also minimizes for its actual degree-one labelled
boundaries. Source: MT Lemma 19.31, pp. 464-466; exact relabelled area range. -/
theorem stabilized_minimum_area_minimizing
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    S.separated.minimum.area = m64LeastAnnulusArea (Q.flow.metric time)
      ((auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ S.approximation.first) ∘
        S.separated.first_label.map)
      ((auxiliaryCircleSection Q (Q.circle.quotient S.separated.offset) ∘
        S.approximation.second) ∘ S.separated.second_label.map) := by
  rw [leastAnnulusArea_comp_lifts_of_C1 (S.lower_smooth.of_le (by simp))
    (S.approximation.first_periodic.comp (auxiliaryCircleSection Q (Q.circle.quotient 0)))
    (S.upper_smooth.of_le (by simp))
    (S.approximation.second_periodic.comp
      (auxiliaryCircleSection Q (Q.circle.quotient S.separated.offset)))
    S.separated.first_label S.separated.second_label]
  exact S.separated.area_minimizing

/-- The actual stabilized approximation and a proved C2 boundary give
the original length comparison with error at most twice the supplied
approximation tolerance. Source: MT Lemma 19.31, pp. 464-466; transport
derivation, Section 13. -/
theorem stabilized_comparison_with_error
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon)
    (htime : time ∈ Icc a b) (hr : 0 < r) (hepsilon : 0 < epsilon)
    (hC2 : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 2 S.separated.minimum.map
      {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1})
    {K mu : ℝ}
    (hsec : ∀ p u v, (Q.flow.connection time).sectionalCurvature p u v ≤ K)
    (hcomparison : ∀ N : IntrinsicAnnulus,
      N.GaussianCurvatureBound K →
      r / 4 < intrinsicBoundaryLength N.metric 1 0 rampPeriod →
      N.SmallBoundaryTurning (7 / 800) (r / 4) →
      intrinsicAnnulusArea N.metric < mu →
        (3 / 4 : ℝ) * intrinsicBoundaryLength N.metric 1 0 rampPeriod ≤
          intrinsicBoundaryLength N.metric 2 0 rampPeriod)
    (harea : S.separated.minimum.area < mu) :
    (3 / 4 : ℝ) * m62Length P.flow (fun y _ => gamma0 y) time ≤
      m62Length P.flow (fun y _ => gamma1 y) time + 2 * epsilon := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  obtain ⟨delta, hdelta, _hquarter, htrim⟩ :=
    exists_stabilized_trimmed_boundary_tolerance S htime hr hC2 (half_pos hepsilon)
  obtain ⟨T, herror0, herror1⟩ := htrim (delta / 2) (half_pos hdelta)
    (half_lt_self hdelta)
  have h := m64_trimmed_boundary_comparison Q.flow time S.separated.minimum
    S.separated.modulus_pos (stabilized_minimum_area_minimizing S) S.separated.conformal
    S.separated.closed_c1 S.separated.interior_smooth
    (fun p hp => (S.separated.within_immersion p hp).2.2) T hsec hcomparison harea
  have hlow := (abs_lt.mp herror0).1
  have hupp := (abs_lt.mp herror1).2
  linarith only [h, hlow, hupp, hepsilon]

end PoincareMT.M64.RampTransport
