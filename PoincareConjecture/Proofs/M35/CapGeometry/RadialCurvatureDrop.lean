import PoincareConjecture.Proofs.M35.CapGeometry.RadialSectionalDerivative
import PoincareConjecture.Proofs.M35.CapGeometry.RadialIntervals

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single (2 : Fin 3) 1

theorem radialMixedSectional_slope_drop
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hsec : D.NonnegativeSectionalCurvature) (hcomplete : MetricComplete g)
    {a b L ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L) (hε : 0 < ε)
    (hbound : ∀ r ∈ Icc a b, D.curvatureDerivativeNorm 1 (r • e2) ≤ L)
    (hpositive : ε ≤ radialMixedCurvatureFactor g a / axisRadialCoefficient g a)
    (hlength : L * (radialArclength g b - radialArclength g a) ≤ ε / 2) :
    axisWarpingRadius g a * (ε / 2) *
      (radialArclength g b - radialArclength g a) ≤ axisWarpingSlope g a := by
  let K (r : ℝ) := radialMixedCurvatureFactor g r / axisRadialCoefficient g r
  let c := axisWarpingRadius g a * (ε / 2)
  have hfloor (r : ℝ) (hr : r ∈ Icc a b) : ε / 2 ≤ K r := by
    have hdiff := abs_radialMixedSectional_sub_le_arclength D hrotation hD ha hr.1
      (fun s hs => hbound s ⟨hs.1, hs.2.trans hr.2⟩)
    have hmono := (radialArclength_strictMono g).monotone hr.2
    have hlen := mul_le_mul_of_nonneg_left
      (show radialArclength g r - radialArclength g a ≤
        radialArclength g b - radialArclength g a by linarith) hL
    have hlow := (abs_le.mp hdiff).1
    dsimp only [K]
    linarith
  have hsecond (r : ℝ) (hr : r ∈ Icc a b) : axisWarpingSecond g r ≤ -c := by
    have hr0 := ha.trans_le hr.1
    have hrho := axisWarpingRadius_monotoneOn D hrotation hsec hcomplete ha hr0 hr.1
    have hmul := mul_le_mul hrho (hfloor r hr) (half_pos hε).le
      (axisWarpingRadius_pos g hr0).le
    have heq : axisWarpingSecond g r = -axisWarpingRadius g r * K r := by
      dsimp only [axisWarpingSecond, K]
      ring
    rw [heq]
    dsimp only [c]
    linarith
  let F (r : ℝ) := axisWarpingSlope g r + c * radialArclength g r
  have hd (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt F (axisRadialSpeed g r * (axisWarpingSecond g r + c)) r := by
    convert! (axisWarpingSlope_hasDerivAt g (ha.trans_le hr.1)).add
      ((radialArclength_hasDerivAt g r).const_mul c) using 1
    dsimp only [axisRadialSpeed]
    ring
  have hanti : AntitoneOn F (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (interior_subset hr)).hasDerivWithinAt)
      (fun r hr => mul_nonpos_of_nonneg_of_nonpos (axisRadialSpeed_pos g r).le
        (by linarith [hsecond r (interior_subset hr)]))
  have h := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hb := axisWarpingSlope_nonneg D hrotation hsec hcomplete (ha.trans_le hab)
  dsimp only [F, c] at h
  linarith

end PoincareConjecture.M35.Uniqueness
