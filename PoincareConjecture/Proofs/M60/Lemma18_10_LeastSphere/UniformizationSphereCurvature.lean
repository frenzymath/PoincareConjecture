import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundVolume
import PoincareConjecture.Proofs.M01.ConnectionExistence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.RetainedTotalCurvature
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Geometry.Riemannian.SpaceForm



theorem roundSphereMetric_eq_induced : m60RoundSphereMetric = roundSphereMetric 2 := by
  rfl



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

end PoincareConjecture.M60

end
