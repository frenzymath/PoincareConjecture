import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.Round.Volume
import PoincareLib.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.Normalization
import PoincareLib.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareLib.Geometry.Riemannian.Surface.Curvature
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.RetainedTotalCurvature
import PoincareLib.Topology.Surface.Triangulation

/-!
# Exact total scalar curvature of the actual sphere metrics

The induced round sphere has sectional curvature one and volume four pi.
Applying the proved intrinsic Gauss-Bonnet formula to the same retained
triangulation for two metrics shows that every smooth sphere metric has
total scalar curvature eight pi.
Source: Moroianu, arXiv:1101.2355, Theorem 5; Morgan-Tian Lemma 18.10,
printed pp. 424-426, uniformization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareMT.M60

open Poincare.Geometry.Riemannian.SpaceForm

/-- Both actual round metrics are the pullback by the same sphere inclusion.
Source: round-sphere reference metric in MT Lemma 18.10. -/
theorem roundSphereMetric_eq_induced : m60RoundSphereMetric = roundSphereMetric 2 := by
  rfl

/-- The actual round two-sphere has scalar curvature two for any compatible
torsion-free connection. Source: MT Lemma 18.10, round reference metric. -/
theorem scalarCurvature_roundSphere (D : LeviCivitaData m60RoundSphereMetric)
    (x : UnitTwoSphere) : D.scalarCurvature x = 2 := by
  change LeviCivitaData (roundSphereMetric 2) at D
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨(roundSphereMetric 2).toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2
    simp
  let b := ((roundSphereMetric 2).orthonormalBasis x).reindex (finCongr hdim)
  rw [D.scalarCurvature_eq_twice_curvatureTensor x b, roundSphereMetric_curvatureTensor]
  have hb (i j : Fin 2) : (roundSphereMetric 2).inner x (b i) (b j) =
      if i = j then 1 else 0 := b.inner_eq_ite i j
  norm_num [hb]

/-- Gauss-Bonnet gives the exact total scalar curvature of every actual
smooth sphere metric. Source: Moroianu, Theorem 5; MT Lemma 18.10. -/
theorem integral_scalarCurvature_sphere (g : RiemannianMetric 2 UnitTwoSphere)
    (D : LeviCivitaData g) :
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) = 8 * Real.pi := by
  obtain ⟨D0⟩ := m01_exists_leviCivitaData m60RoundSphereMetric
  obtain ⟨T⟩ := Topology.Surface.exists_finite_smooth_triangulation_with_retained_coordinates
    (M := UnitTwoSphere)
  have heq := (T.integral_scalarCurvature_eq_four_pi_euler_of_length_lt_one D T.length_lt_one).trans
    (T.integral_scalarCurvature_eq_four_pi_euler_of_length_lt_one D0 T.length_lt_one).symm
  rw [heq]
  simp only [scalarCurvature_roundSphere, integral_const, smul_eq_mul,
    m60RoundSphereMetric_volume_univ]
  ring

end PoincareMT.M60

end
