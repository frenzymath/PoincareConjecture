import PoincareConjecture.Proofs.M35.CapGeometry.RadialCurvatureDrop

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e2 : StandardCapSpace := EuclideanSpace.single (2 : Fin 3) 1

theorem radialMixedSectional_tendsto_zero_of_slope
    (g : ℕ → RiemannianMetric 3 StandardCapSpace)
    (D : ∀ k, LeviCivitaData (g k))
    (hD : ∀ k, (D k).CurvatureTensorCalculus)
    (hrotation : ∀ k, ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (g k).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (g k).inner x u v)
    (hsec : ∀ k, (D k).NonnegativeSectionalCurvature)
    (hcomplete : ∀ k, MetricComplete (g k))
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k)
    {ρ d L : ℝ} (hρ : 0 < ρ) (hd : 0 < d) (hL : 0 < L)
    (hradius : ∀ k, ρ ≤ axisWarpingRadius (g k) (a k))
    (hbound : ∀ k r, a k ≤ r →
      radialArclength (g k) r - radialArclength (g k) (a k) ≤ d →
        (D k).curvatureDerivativeNorm 1 (r • e2) ≤ L)
    (hslope : Tendsto (fun k => axisWarpingSlope (g k) (a k)) atTop (𝓝 0)) :
    Tendsto (fun k => radialMixedCurvatureFactor (g k) (a k) /
      axisRadialCoefficient (g k) (a k)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun k => hb.trans_le
      (div_nonneg (radialMixedCurvatureFactor_nonneg (D k) (hrotation k) (hsec k) (ha k))
        (axisRadialCoefficient_pos (g k) (a k)).le)
  · intro ε hε
    let ell := min d (ε / (2 * L))
    have hell : 0 < ell := lt_min hd (by positivity)
    have helld : ell ≤ d := min_le_left _ _
    have hLell : L * ell ≤ ε / 2 := by
      have h := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp
        (min_le_right d (ε / (2 * L)))
      dsimp only [ell]
      linarith
    let δ := ρ * (ε / 2) * ell
    have hδ : 0 < δ := by dsimp only [δ]; positivity
    filter_upwards [hslope.eventually (eventually_lt_nhds hδ)] with k hk
    by_contra hbad
    obtain ⟨b, hab, hlength⟩ := exists_outward_radial_interval (g k) (hcomplete k)
      (ha k).le hell
    have hbnd (r : ℝ) (hr : r ∈ Icc (a k) b) :
        (D k).curvatureDerivativeNorm 1 (r • e2) ≤ L := by
      apply hbound k r hr.1
      have hs := (radialArclength_strictMono (g k)).monotone hr.2
      linarith
    have hdrop := radialMixedSectional_slope_drop (D k) (hD k) (hrotation k)
      (hsec k) (hcomplete k) (ha k) hab.le hL.le hε hbnd (le_of_not_gt hbad)
      (by rw [hlength]; exact hLell)
    rw [hlength] at hdrop
    have hρmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hradius k) (half_pos hε).le) hell.le
    dsimp only [δ] at hk
    linarith

end PoincareConjecture.M35.Uniqueness
