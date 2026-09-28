import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.Maximal
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Domain.Metric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem domainCalculus
    (H : CompatibleSpacetimeTheory.{u, v} R.spacetime R.timeIntervals) :
    ParabolicDomainCalculus (domainTransport.{u, v} R Q hQ a) := by
  let D := domainTransport.{u, v} R Q hQ a
  refine {
    worldline_image := domain_worldline_image D
    embedding_image := domain_embedding_image D
    cylinder_image := domain_cylinder_image D
    embedding_based := domain_embedding_based D
    cylinder_based := domain_cylinder_based D
    worldline_time_restrict := domain_worldline_restrict D
    embedding_time_restrict := domain_embedding_restrict D
    cylinder_time_restrict := domain_cylinder_restrict D
    embedding_source_restrict := ?_
    cylinder_open_restrict := ?_
    relative_time_open_iff := relative_time_open_iff Q hQ a
    time_cover_iff := time_cover_iff Q hQ a
    cylinder_glue := ?_
    worldline_maximal_iff := domain_worldline_maximal D
    embedding_maximal_iff := domain_embedding_maximal D
    cylinder_metric_exists := domain_cylinder_metric_exists H
    cylinder_metric := domain_cylinder_metric }
  · intro C C' _ _ K e r j hr s x
    rw [D.embedding_forward, D.embedding_forward, hr]
  · intro C _ _ _ K e U r hr s x
    rw [D.cylinder_forward, D.cylinder_forward, hr]
  · intro C _ _ _ K B J h e localCylinder he b s x
    exact (domain_cylinder_restrict D C K (J b) (h b) e (localCylinder b)
      (fun t y ↦ (he b t y).symm) s x).symm

end PoincareConjecture.ParabolicRescaling
