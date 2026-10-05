import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Derivative.Second.DirectionalDerivative
import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.Conformal.Area
import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.Stereographic.LogDensity

/-!
# The logarithmic conformal factor and its plane density

Morgan-Tian Claim 18.12, printed pp. 426-427, coordinate curvature
derivation. At a positive-factor point the logarithm of the intrinsic
factor is log(area density)-log(round density). Differentiating this
local identity supplies the source curvature contribution 2*sigma.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A smooth weakly conformal sphere has smooth actual plane area
density, including its branches. Source: MT Claim 18.12, pp. 426-427. -/
theorem m60SphereAreaDensity_contDiff (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hc : M60WeaklyConformal g f) : ContDiff ℝ ∞ (m60SphereAreaDensity g f) := by
  have heq : m60SphereAreaDensity g f = fun z =>
      m60SphereConformalFactor g f (m60SphereParameter z) *
        (16 / (‖z‖ ^ 2 + 4) ^ 2) :=
    funext (m60SphereAreaDensity_eq_conformalFactor_mul g f (hf.of_le (by simp)) hc)
  rw [heq]
  have hq : ContDiff ℝ ∞ (m60SphereConformalFactor g f ∘ m60SphereParameter) :=
    contMDiff_iff_contDiff.mp
      ((m60SphereConformalFactor_contMDiff g f hf hc).comp m60SphereParameter_contMDiff)
  exact hq.mul (contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
    (by intro z; positivity))

/-- The logarithmic intrinsic factor's round Laplacian is the plane
log-area Laplacian plus the explicit source term, divided by sigma.
Source: MT Claim 18.12, pp. 426-427, coordinate curvature derivation. -/
theorem m60Sphere_logConformalFactor_laplacian
    (D : LeviCivitaData m60RoundSphereMetric) (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hc : M60WeaklyConformal g f) (z : LoopPlane)
    (hz : 0 < m60SphereConformalFactor g f (m60SphereParameter z)) :
    (16 / (‖z‖ ^ 2 + 4) ^ 2) * D.laplacian
        (fun p => Real.log (m60SphereConformalFactor g f p)) (m60SphereParameter z) =
      (∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ
        (fun x => Real.log (m60SphereAreaDensity g f x)) y
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) z
            (EuclideanSpace.basisFun (Fin 2) ℝ i)) + 2 * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  have hq := m60SphereConformalFactor_contMDiff g f hf hc
  have ha := m60SphereAreaDensity_contDiff g f hf hc
  have haz : 0 < m60SphereAreaDensity g f z := by
    rw [m60SphereAreaDensity_eq_conformalFactor_mul g f (hf.of_le (by simp)) hc]
    exact mul_pos hz (by positivity)
  have hlog : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p => Real.log (m60SphereConformalFactor g f p)) (m60SphereParameter z) :=
    (Real.contDiffAt_log.mpr hz.ne').contMDiffAt.comp _ (hq _)
  have heq : ((fun p => Real.log (m60SphereConformalFactor g f p)) ∘ m60SphereParameter)
      =ᶠ[𝓝 z] (fun x => Real.log (m60SphereAreaDensity g f x) -
        Real.log (16 / (‖x‖ ^ 2 + 4) ^ 2)) := by
    have hcont := hq.continuous.comp m60SphereParameter_contMDiff.continuous
    filter_upwards [hcont.continuousAt.eventually_ne hz.ne'] with y hy
    dsimp only [Function.comp_apply] at hy ⊢
    rw [m60SphereAreaDensity_eq_conformalFactor_mul g f (hf.of_le (by simp)) hc,
      Real.log_mul hy (by positivity)]
    simp only [add_sub_cancel_right]
  rw [m60RoundSphere_laplacian_stereographic D z hlog]
  have hsecond (i : Fin 2) := M60.second_fderiv_congr heq
    (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)
  simp_rw [hsecond, M60.second_fderiv_sub
    ((ha.contDiffAt.log haz.ne').of_le (WithTop.coe_le_coe.mpr le_top))
    (m60SphereParameter_logDensity_contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  rw [Finset.sum_sub_distrib, m60SphereParameter_logDensity_laplacian]
  ring

end PoincareMT
