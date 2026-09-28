import PoincareConjecture.Proofs.M47.TerminalCurvatureCalibratedNeck
import PoincareConjecture.Proofs.M47.TerminalCurvatureSmoothLift
import PoincareConjecture.Proofs.M02.SphereConnectivity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47



theorem terminalCurvature_lifted_calibrated_neck_sphere
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
    (D : LeviCivitaData g) (E : LeviCivitaData h)
    (projection : N → M) (hcover : IsCoveringMap projection)
    (hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ projection)
    (hmetric : ∀ x v w, h.inner x v w = g.inner (projection x)
      (mfderiv (𝓡 3) (𝓡 3) projection x v)
      (mfderiv (𝓡 3) (𝓡 3) projection x w))
    (neck : EpsilonNeck g) (hsmall : neck.epsilon ≤ 1 / 200)
    (theta0 : UnitTwoSphere) (p0 : N)
    (hp0 : projection p0 = neck.coordinate_map (theta0, 0)) :
    ∃ F : UnitTwoSphere → N,
      ContMDiff (𝓡 2) (𝓡 3) ∞ F ∧ F theta0 = p0 ∧
      (∀ theta, projection (F theta) = neck.coordinate_map (theta, 0)) ∧
      IsCompact (range F) ∧ (range F).Nonempty ∧
      ∀ theta, ∃ a b : TangentSpace (𝓡 2) theta,
        0 < E.curvatureTensor (F theta)
          (mfderiv (𝓡 2) (𝓡 3) F theta a) (mfderiv (𝓡 2) (𝓡 3) F theta b)
          (mfderiv (𝓡 2) (𝓡 3) F theta a) (mfderiv (𝓡 2) (𝓡 3) F theta b) := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    PoincareConjecture.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank
      (E := EuclideanSpace ℝ (Fin 3)) (by simp)
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  obtain ⟨F, hF, hF0, hproj, hderiv⟩ := terminalCurvature_exists_smooth_cover_lift
    hcover hlocal (fun theta => neck.coordinate_map (theta, 0))
    (terminalCurvature_neck_sphere_geometry neck).1 theta0 p0 hp0
  refine ⟨F, hF, hF0, hproj, isCompact_range hF.continuous,
    ⟨F theta0, mem_range_self theta0⟩, ?_⟩
  intro theta
  obtain ⟨a, b, hab⟩ := terminalCurvature_calibrated_neck_positive_plane D neck hsmall theta
  refine ⟨a, b, ?_⟩
  rw [E.curvatureTensor_eq_of_local_isometry D isOpen_univ hlocal.contMDiff.contMDiffOn
    (fun x _ v w => hmetric x v w) (mem_univ (F theta))]
  have ha := congrArg (fun L => L a) (hderiv theta)
  have hb := congrArg (fun L => L b) (hderiv theta)
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [ha, hb]
  let va : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun theta => neck.coordinate_map (theta, 0)) theta a
  let vb : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun theta => neck.coordinate_map (theta, 0)) theta b
  have heq := congrArg (fun x : M => D.curvatureTensor x va vb va vb) (hproj theta)
  exact heq.symm ▸ hab

end PoincareConjecture.M47
