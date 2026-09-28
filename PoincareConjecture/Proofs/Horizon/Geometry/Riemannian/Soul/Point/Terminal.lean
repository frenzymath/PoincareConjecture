import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Busemann.Rigidity








noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]


theorem exists_singleton_horoball_of_strictlyPositiveSectionalCurvature
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hpos : D.StrictlyPositiveSectionalCurvature) :
    letI := g.toMetricSpace
    ∃ (p o : M) (c : ℝ),
      Poincare.Riemannian.Soul.horoballIntersection o c = {p} ∧
      TotallyConvexSet g ({p} : Set M) := by
  classical
  let := g.toMetricSpace
  let p := Classical.arbitrary M
  have hsec : D.NonnegativeSectionalCurvature := hpos.nonnegative
  obtain ⟨R, _, hSne, _, _, _, hSinterior, hshift, hSconvex⟩ :=
    g.exists_maximal_innerParallelSet_of_nonnegativeSectional D hcomplete hsec
      (fun _ _ => rfl) p (c := 1) zero_lt_one
  let S := {x ∈ Poincare.Riemannian.Soul.horoballIntersection p 1 |
    R ≤ Metric.infDist x (Poincare.Riemannian.Soul.horoballIntersection p 1)ᶜ}
  change S.Nonempty at hSne
  change interior S = ∅ at hSinterior
  change S = Poincare.Riemannian.Soul.horoballIntersection p (1 - R) at hshift
  change TotallyConvexSet g S at hSconvex
  have hsub : S.Subsingleton := by
    rw [hshift] at hSinterior ⊢
    exact g.subsingleton_horoballIntersection_of_empty_interior D hcomplete hsec
      (fun _ _ => rfl) hpos p (1 - R) hSinterior
  obtain ⟨q, hq⟩ := hSne
  have hsingleton : S = {q} := Set.Subset.antisymm
    (fun y hy => mem_singleton_iff.mpr (hsub hy hq)) (singleton_subset_iff.mpr hq)
  exact ⟨q, p, 1 - R, hshift.symm.trans hsingleton,
    by simpa only [TotallyConvexSet, ← hsingleton] using hSconvex⟩







theorem exists_point_soul_of_strictlyPositiveSectionalCurvature
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hpos : D.StrictlyPositiveSectionalCurvature) :
    ∃ p : M, TotallyConvexSet g ({p} : Set M) := by
  obtain ⟨p, _, _, _, hp⟩ :=
    g.exists_singleton_horoball_of_strictlyPositiveSectionalCurvature D hcomplete hpos
  exact ⟨p, hp⟩

end PoincareConjecture.RiemannianMetric
