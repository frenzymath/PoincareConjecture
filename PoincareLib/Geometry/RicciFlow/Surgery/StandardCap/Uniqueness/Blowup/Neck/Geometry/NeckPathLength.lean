import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Neck.Curvature.NeckAxialDerivative
import PoincareLib.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance
import PoincareLib.Geometry.Riemannian.MetricComparison

/-!
# Axial displacement versus actual neck path length

Morgan-Tian Theorem 12.28, pp. 323-324. Integrating the actual inverse
coordinate differential bounds axial displacement by twice the length
of every smooth path retained in the actual neck carrier.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareMT.StandardCylinderPatch

/-- Theorem 12.28, pp. 323-324: a retained neck path has axial displacement
at most twice its actual Riemannian length. -/
theorem axial_edist_le_pathELength {epsilon u : ℝ} {x : StandardCapSpace}
    (N : StandardCylinderPatch epsilon⁻¹ x) (g : RiemannianMetric 3 StandardCapSpace)
    (he : 0 < epsilon) (hesmall : epsilon ≤ 1 / 24) (hu : u ∈ Icc (-1) 0)
    (hclose : RoundCylinderClose epsilon u (roundCylinderPullback g N.coordinate))
    (gamma : ℝ → StandardCapSpace)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1))
    (himage : MapsTo gamma (Icc 0 1) N.carrier) :
    edist (N.inverse (gamma 0)).2 (N.inverse (gamma 1)).2 ≤
      2 * g.pathELength gamma 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm (z : StandardCapSpace) (v : TangentSpace (𝓡 3) z) :
      ‖v‖ = g.tangentNorm z v := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hbound (z : StandardCapSpace) (hz : z ∈ N.carrier) :
      ‖mvfderiv (𝓡 3) (fun y => (N.inverse y).2) z‖ₑ ≤ (2 : ℝ≥0∞) := by
    apply ContinuousLinearMap.opENorm_le_bound
    intro v
    have hb := ENNReal.ofReal_le_ofReal (N.axial_derivative_bound g he hesmall hu hclose hz v)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hb
    simpa only [← ofReal_norm, hnorm, Real.norm_eq_abs, ENNReal.ofReal_ofNat] using hb
  exact Poincare.edist_le_mul_pathELength_of_mfderiv_le
    (M := StandardCapSpace) (E := EuclideanSpace ℝ (Fin 3)) (F := ℝ)
    (I := 𝓡 3) (f := fun y => (N.inverse y).2) (s := N.carrier) (K := (2 : ℝ≥0))
    (fun z hz => (N.axial_contMDiffAt hz).of_le (by simp))
    (fun z hz => by exact hbound z hz) hgamma himage

end PoincareMT.StandardCylinderPatch
