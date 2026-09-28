import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.Global
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.TrajectoryCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.DistanceCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalSphere








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]



theorem exists_radialHomeomorph_of_singleton_horoball_of_spherical_level
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {o p : M} {c : ℝ}
    (hlevel : letI := g.toMetricSpace;
      Poincare.Riemannian.Soul.horoballIntersection o c = {p})
    (hsphere : ∃ r : ℝ, 0 < r ∧
      Nonempty (UnitTwoSphere ≃ₜ {y : M // (g.edist p y).toReal = r})) :
    Nonempty (RadialHomeomorph g p) := by
  let := g.toMetricSpace
  obtain ⟨r, hr, ⟨S⟩⟩ := hsphere
  obtain ⟨_, _, _, _, Φ, _, _, _, _, _, _, _, _, _, _, _, hzero, _, hadd, hs,
    hfix, hmono, hsurj⟩ :=
    g.exists_complete_outward_flow_of_singleton_horoball D hc hsec hlevel
  obtain ⟨F, hF⟩ := Poincare.Topology.exists_trajectory_level_homeomorph
    Φ hs.continuous hzero hadd p hfix (fun y => (g.edist p y).toReal)
    (g.continuous_toReal_edist p) (dist_self p)
    (fun y hyp => dist_pos.mpr (Ne.symm hyp)) hmono hsurj hr
  let G : (UnitTwoSphere × Ioi (0 : ℝ)) ≃ₜ {y : M // y ≠ p} :=
    (S.prodCongr Real.expOrderIso.toHomeomorph.symm).trans F
  have hG (θ : UnitTwoSphere) (t : Ioi (0 : ℝ)) :
      (G (θ, t)).val = Φ (Real.expOrderIso.symm t) (S θ).val :=
    hF (S θ, Real.expOrderIso.symm t)
  have haway (θ : UnitTwoSphere) : (S θ).val ≠ p := by
    intro heq
    have h := (S θ).property
    rw [heq] at h
    change dist p p = r at h
    rw [dist_self] at h
    exact hr.ne' h.symm
  refine ⟨RadialHomeomorph.of_monotone_trajectories G ?_ ?_⟩
  · intro θ s t hst
    change (g.edist p (G (θ, s)).val).toReal < (g.edist p (G (θ, t)).val).toReal
    rw [hG, hG]
    exact hmono (S θ).val (haway θ) (Real.expOrderIso.symm.strictMono hst)
  · intro θ s hspos
    obtain ⟨t, ht⟩ := hsurj (S θ).val (haway θ) s hspos
    refine ⟨Real.expOrderIso t, ?_⟩
    change (g.edist p (G (θ, Real.expOrderIso t)).val).toReal = s
    rw [hG, Real.expOrderIso.symm_apply_apply]
    exact ht



theorem exists_radialHomeomorph_of_singleton_horoball
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {o p : M} {c : ℝ}
    (hlevel : letI := g.toMetricSpace;
      Poincare.Riemannian.Soul.horoballIntersection o c = {p}) :
    Nonempty (RadialHomeomorph g p) :=
  g.exists_radialHomeomorph_of_singleton_horoball_of_spherical_level D hc hsec hlevel
    (g.exists_small_distance_sphere_homeomorph p)

end PoincareConjecture.RiemannianMetric
