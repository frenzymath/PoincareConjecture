import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}

theorem canonicalRamp_periodic (P : M62.CircleProductData F circumference)
    {gamma : ℝ → M} (hgamma : Function.Periodic gamma curvePeriod) :
    Function.Periodic (m63CanonicalRamp P gamma) curvePeriod := by
  intro x
  apply Prod.ext
  · exact hgamma x
  · have hperiod : curvePeriod ≠ 0 := ne_of_gt Real.two_pi_pos
    have hshift : circumference * (x + curvePeriod) / curvePeriod =
        circumference * x / curvePeriod + circumference := by field_simp
    change ((circumference * (x + curvePeriod) / curvePeriod : ℝ) : AddCircle circumference) = _
    rw [hshift, AddCircle.coe_add_period]
    rfl

theorem canonicalRamp_contMDiff (P : M62.CircleProductData F circumference)
    {gamma : ℝ → M} {k : WithTop ℕ∞} (hk : k ≤ ∞)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) k gamma) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) k (m63CanonicalRamp P gamma) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hphi : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) k
      (fun x : ℝ => circumference * x / curvePeriod) :=
    contMDiff_iff_contDiff.mpr ((contDiff_const.mul contDiff_id).div_const _)
  exact (P.charts.from_product_smooth.of_le hk).comp
    (hgamma.prodMk ((P.circle.quotient_smooth.of_le hk).comp hphi))

theorem canonicalRamp_velocity (P : M62.CircleProductData F circumference)
    {gamma : ℝ → M} {x : ℝ} (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x) :
    P.charts.split (m63CanonicalRamp P gamma x) (curveVelocity (m63CanonicalRamp P gamma) x) =
      (curveVelocity gamma x,
        (circumference / curvePeriod) • P.circle.frame (m63CanonicalRamp P gamma x).2) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let phi : ℝ → ℝ := fun y => circumference * y / curvePeriod
  have hphi : HasDerivAt phi (circumference / curvePeriod) x := by
    simpa [phi] using ((hasDerivAt_id x).const_mul circumference).div_const curvePeriod
  have hcircle : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1)
      (fun y => P.circle.quotient (phi y)) x :=
    (P.circle.quotient_smooth.mdifferentiableAt (by simp)).comp x
      hphi.differentiableAt.mdifferentiableAt
  have hgraph : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1))
      (m63CanonicalRamp P gamma) x :=
    (P.charts.from_product_smooth.mdifferentiableAt (by simp)).comp x
      (hgamma.prodMk hcircle)
  apply Prod.ext
  · rw [P.charts.split_space]
    have h := mfderiv_comp_apply (f := m63CanonicalRamp P gamma)
      (g := (Prod.fst : P.charts.Point → M)) x
      ((contMDiff_fst.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hgraph 1
    exact h.symm
  · rw [P.charts.split_circle]
    have h := mfderiv_comp_apply (f := m63CanonicalRamp P gamma)
      (g := (Prod.snd : P.charts.Point → P.circle.Point)) x
      ((contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hgraph 1
    have hvelocity : curveVelocity (fun y => P.circle.quotient (phi y)) x =
        (circumference / curvePeriod) • P.circle.frame (P.circle.quotient (phi x)) := by
      exact (curveVelocity_comp (gamma := P.circle.quotient)
        (P.circle.quotient_smooth.mdifferentiableAt (by simp)) hphi).trans
        (congrArg ((circumference / curvePeriod) • ·) (P.circle.frame_quotient (phi x)).symm)
    exact h.symm.trans hvelocity

theorem canonicalRamp_degree_one (P : M62.CircleProductData F circumference)
    (gamma : ℝ → M) :
    ∃ L : M63PositiveDegreeLift P (m63CanonicalRamp P gamma), L.degree = 1 := by
  have hperiod : curvePeriod ≠ 0 := ne_of_gt Real.two_pi_pos
  have hderiv (x : ℝ) : HasDerivAt
      (fun y : ℝ => circumference * y / curvePeriod) (circumference / curvePeriod) x := by
    simpa using ((hasDerivAt_id x).const_mul circumference).div_const curvePeriod
  refine ⟨{
    lift := fun x => circumference * x / curvePeriod
    regular := (contDiff_const.mul contDiff_id).div_const _
    degree := 1
    degree_positive := Nat.zero_lt_one
    quotient_eq := fun _ => rfl
    period_shift := ?_
    derivative_positive := fun x => ?_ }, rfl⟩
  · intro x
    simp only [Nat.cast_one, one_mul]
    field_simp
  · rw [(hderiv x).deriv]
    exact div_pos P.circle.positive Real.two_pi_pos

end PoincareConjecture.M63
