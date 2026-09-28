import PoincareConjecture.Proofs.M35.CapGeometry.RadialEndSlope

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

theorem axisWarpingRadius_sq_le_or_mul_arclength_le
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hsec : D.NonnegativeSectionalCurvature) (hcomplete : MetricComplete g)
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (hfloor : ∀ r ∈ Icc a b,
      c ≤ D.scalarCurvature (r • EuclideanSpace.single (2 : Fin 3) 1)) :
    axisWarpingRadius g a ^ 2 ≤ 4 / c ∨
      c * axisWarpingRadius g a * (radialArclength g b - radialArclength g a) ≤ 8 := by
  by_cases hsmall : axisWarpingRadius g a ^ 2 ≤ 4 / c
  · exact Or.inl hsmall
  right
  have hlarge : 4 < c * axisWarpingRadius g a ^ 2 := by
    have h := (div_lt_iff₀ hc).mp (lt_of_not_ge hsmall)
    nlinarith
  have hsecond (u : ℝ) (hu : u ∈ Icc a b) :
      axisWarpingSecond g u ≤ -(c * axisWarpingRadius g a / 8) := by
    have hu0 : 0 < u := ha.trans_le hu.1
    have hupos := axisWarpingRadius_pos g hu0
    have hfu := axisWarpingRadius_monotoneOn D hrotation hsec hcomplete ha hu0 hu.1
    have hscalar := hfloor u hu
    rw [rotational_scalar_axis D hrotation hu0] at hscalar
    have hscalar' : c ≤
        2 * (1 - axisWarpingSlope g u ^ 2) / axisWarpingRadius g u ^ 2 -
          4 * axisWarpingSecond g u / axisWarpingRadius g u := by
      calc
        c ≤ _ := hscalar
        _ = _ := by
          rw [show 2 * radialTangentialCurvatureFactor g u / axisAngularCoefficient g u =
              2 * (radialTangentialCurvatureFactor g u / axisAngularCoefficient g u) by ring,
            show 4 * radialMixedCurvatureFactor g u / axisRadialCoefficient g u =
              4 * (radialMixedCurvatureFactor g u / axisRadialCoefficient g u) by ring,
            radialTangentialCurvatureFactor_eq_warping g hu0,
            radialMixedCurvatureFactor_eq_warping g hu0]
          ring
    have hscaled := mul_le_mul_of_nonneg_right hscalar'
      (sq_nonneg (axisWarpingRadius g u))
    have heq :
        (2 * (1 - axisWarpingSlope g u ^ 2) / axisWarpingRadius g u ^ 2 -
          4 * axisWarpingSecond g u / axisWarpingRadius g u) *
            axisWarpingRadius g u ^ 2 =
          2 * (1 - axisWarpingSlope g u ^ 2) -
            4 * axisWarpingSecond g u * axisWarpingRadius g u := by
      field_simp [hupos.ne']
    rw [heq] at hscaled
    have hsecond' : 4 * axisWarpingSecond g u ≤
        2 / axisWarpingRadius g u - c * axisWarpingRadius g u := by
      apply le_of_mul_le_mul_right (a := axisWarpingRadius g u) _ hupos
      have hcancel : 2 / axisWarpingRadius g u * axisWarpingRadius g u = 2 :=
        div_mul_cancel₀ _ hupos.ne'
      nlinarith [sq_nonneg (axisWarpingSlope g u)]
    have hinv : 2 / axisWarpingRadius g u ≤ 2 / axisWarpingRadius g a :=
      div_le_div_of_nonneg_left (by norm_num) (axisWarpingRadius_pos g ha) hfu
    have hmul : c * axisWarpingRadius g a ≤ c * axisWarpingRadius g u :=
      mul_le_mul_of_nonneg_left hfu hc.le
    have hhalf : 2 / axisWarpingRadius g a ≤ c * axisWarpingRadius g a / 2 := by
      apply (div_le_iff₀ (axisWarpingRadius_pos g ha)).mpr
      nlinarith
    linarith
  let K := c * axisWarpingRadius g a / 8
  let F (u : ℝ) := axisWarpingSlope g u + K * radialArclength g u
  have hd (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivAt F (axisRadialSpeed g u * (axisWarpingSecond g u + K)) u := by
    convert! (axisWarpingSlope_hasDerivAt g (ha.trans_le hu.1)).add
      ((radialArclength_hasDerivAt g u).const_mul K) using 1
    dsimp only [axisRadialSpeed]
    ring
  have hanti : AntitoneOn F (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
      (fun u hu => mul_nonpos_of_nonneg_of_nonpos (axisRadialSpeed_pos g u).le
        (by dsimp only [K]; linarith [hsecond u (interior_subset hu)]))
  have h := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  dsimp only [F, K] at h
  have hb := axisWarpingSlope_nonneg D hrotation hsec hcomplete (ha.trans_le hab)
  have ha' := axisWarpingSlope_le_one D hrotation hsec ha
  nlinarith

end PoincareConjecture.M35.Uniqueness
