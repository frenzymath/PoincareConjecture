import PoincareLib.Geometry.RicciFlow.CurveShortening.Slope.Laws
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.Continuity
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.Periodicity
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates

/-!
# Regularity and periodicity of the actual circle slope

The scalar quantities in Claim 19.11 and Corollary 19.13, MT2007 p. 446,
are computed from the same displayed curve and product metric. M62 supplies
the raw field regularity. Reciprocal positive speed gives closed-cylinder
continuity and interior smoothness without any assumed slope sign.
See `proof-work/tasks/M63/derivations/2026-09-21-smooth-slope-preservation.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

omit [IsManifold (𝓡 n) ∞ M] in
/-- Periodic differentiable curves have periodic actual velocity in the
underlying tangent model. Metric pairings must also retain the equal
basepoints. This is the shift calculation used in MT2007 Corollary 19.13. -/
theorem m63CurveVelocity_periodic {gamma : ℝ → M} {p : ℝ}
    (hgamma : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) gamma)
    (hper : Function.Periodic gamma p) :
    Function.Periodic (fun x => (curveVelocity gamma x : EuclideanSpace ℝ (Fin n))) p := by
  intro x
  have hshift : HasDerivAt (fun y : ℝ => y + p) 1 x := (hasDerivAt_id x).add_const p
  have hvalue : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => y + p) x 1 = 1 := by
    rw [mfderiv_eq_fderiv, hshift.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ 1
  have hcomp := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1)
    (mfderiv_comp (f := fun y : ℝ => y + p) (g := gamma) x (hgamma (x + p))
      hshift.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => gamma (y + p)) x 1 =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma (x + p)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => y + p) x 1) at hcomp
  rw [hvalue, funext hper] at hcomp
  exact hcomp.symm

/-- The slope of an existing smooth solution is jointly continuous through
the time endpoints. Claim 19.11 and Corollary 19.13, MT2007 p. 446. -/
theorem m63Slope_continuousOn {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) :
    ContinuousOn (fun z : ℝ × ℝ => m62Slope P c z.2 z.1) (univ ×ˢ Icc a b) := by
  let := P.charts.chartedSpace
  have hB := (M62.circleProduct_identities P).circle_unit_smooth.continuous.continuousOn.comp
    hc.continuous (fun _ _ => mem_univ _)
  have hpair := M62.metric_pairing_continuousOn P.flow c hc.continuous _ _
    hc.velocity_continuous hB
  have hinv := (M62.speed_continuousOn P.flow c hc).inv₀
    (fun z hz => (M62.speed_pos P.flow c hc hz.2 z.1).ne')
  simpa only [Pi.mul_def, Pi.inv_def, m62Slope, spatialUnitTangent,
    map_smul, smul_apply, smul_eq_mul]
    using hinv.mul hpair

/-- The actual slope is jointly smooth at interior times, without assuming
that it is positive. Claim 19.11, MT2007 p. 446. -/
theorem m63Slope_contDiffOn {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => m62Slope P c z.2 z.1) (univ ×ˢ Ioo a b) := by
  let := P.charts.chartedSpace
  have hB := (M62.circleProduct_identities P).circle_unit_smooth.comp_contMDiffOn
    hc.joint_smooth
  have hpair := M62.metric_pairing_contDiffOn P.flow c hc.joint_smooth _ _
    (M62.spatial_velocity_joint_contMDiff P.flow c hc) hB
  have hinv := (M62.speed_joint_contDiffOn P.flow c hc).inv
    (fun z hz => (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self hz.2) z.1).ne')
  simpa only [Pi.mul_def, Pi.inv_def, m62Slope, spatialUnitTangent,
    map_smul, smul_apply, smul_eq_mul]
    using hinv.mul hpair

/-- The slope inherits the actual curve's angular period at every included
time, including the endpoints. Corollary 19.13, MT2007 p. 446. -/
theorem m63Slope_periodic {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (m62Slope P c t) curvePeriod := by
  let := P.charts.chartedSpace
  have hv := m63CurveVelocity_periodic
    (fun x => (hc.spatial_regular t ht x).mdifferentiableAt (by norm_num))
    (hc.periodic t ht)
  intro x
  have hvx : curveVelocity (fun y => c y t) (x + curvePeriod) =
      curveVelocity (fun y => c y t) x := hv x
  simp only [m62Slope, spatialUnitTangent]
  rw [M62.speed_periodic P.flow c hc ht x, hvx, hc.periodic t ht x]

/-- Ramp positivity of a displayed time slice is literally positivity of
the same curve's slope. Definition 19.12, MT2007 p. 446. -/
theorem m63IsRampAt_slice_iff {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point) (t : ℝ) :
    M63IsRampAt P (fun x => c x t) t ↔ ∀ x, 0 < m62Slope P c t x := by
  rfl

end PoincareMT
