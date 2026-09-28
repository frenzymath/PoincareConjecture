import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.SphereApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.ConeTopology










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology NNReal ENNReal Manifold ContDiff

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] [ProperSpace X] {p : X}



theorem exists_dense_based_ray_sequence (hc : RayComparison p)
    (hne : Nonempty (basedMinimizingRays p)) :
    ∃ η : ℕ → basedMinimizingRays p,
      DenseRange (fun j => asymptoticLinkProjection hc (η j)) ∧
      DenseRange (fun j => asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))) := by
  classical
  let : Nonempty (AsymptoticLink p hc) :=
    ⟨asymptoticLinkProjection hc hne.some⟩
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq (AsymptoticLink p hc)
  choose η hη using fun j => surjective_asymptoticLinkProjection hc (a j)
  have heq : (fun j => asymptoticLinkProjection hc (η j)) = a := funext hη
  have hd : DenseRange (fun j => asymptoticLinkProjection hc (η j)) := heq.symm ▸ ha
  refine ⟨η, hd, ?_⟩
  exact (surjective_asymptoticConeUnitProjection hc).denseRange.comp hd
    (isometry_asymptoticConeUnitProjection hc).continuous


theorem exists_finite_ray_net_of_dense (hc : RayComparison p)
    (η : ℕ → basedMinimizingRays p)
    (hd : DenseRange (fun j => asymptoticLinkProjection hc (η j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z : AsymptoticLink p hc, ∃ j ≤ N,
      dist z (asymptoticLinkProjection hc (η j)) < ε := by
  classical
  have hcover : (univ : Set (AsymptoticLink p hc)) ⊆
      ⋃ j : ℕ, Metric.ball (asymptoticLinkProjection hc (η j)) ε := by
    intro z _
    obtain ⟨j, hj⟩ := hd.exists_dist_lt z hε
    exact mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun j => Metric.ball (asymptoticLinkProjection hc (η j)) ε)
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨s.sup id, ?_⟩
  intro z
  obtain ⟨j, hjz⟩ := mem_iUnion.mp (hs (mem_univ z))
  obtain ⟨hj, hz⟩ := mem_iUnion.mp hjz
  exact ⟨j, Finset.le_sup (f := id) hj, hz⟩

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio



theorem exists_dense_ray_sequence_with_source_sphere_nets
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M) :
    letI := g.toMetricSpace
    let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
    ∃ η : ℕ → basedMinimizingRays p,
      DenseRange (fun j => asymptoticLinkProjection hc (η j)) ∧
      DenseRange (fun j => asymptoticConeUnitProjection hc (asymptoticLinkProjection hc (η j))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ L₀ : ℝ, 0 < L₀ ∧
        ∀ L : ℝ, L₀ ≤ L → ∀ x : M, (g.edist p x).toReal = L →
          ∃ j ≤ N, (g.edist x (rayExtension (η j) L)).toReal / L < ε := by
  classical
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hcomplete
  let hc := g.rayComparison_of_metricComplete D hcomplete hsec p
  obtain ⟨η, hd, hdu⟩ := exists_dense_based_ray_sequence hc
    (g.nonempty_basedMinimizingRays hcomplete p)
  refine ⟨η, hd, hdu, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_finite_ray_net_of_dense hc η hd (show 0 < ε / 2 by positivity)
  obtain ⟨L₀, hL₀, hrel⟩ :=
    g.exists_sphereLinkRelation_approximation_of_metricComplete D hcomplete hsec p
      (show 0 < ε / 2 by positivity)
  refine ⟨N, L₀, hL₀, ?_⟩
  intro L hL x hx
  have hLpos : 0 < L := hL₀.trans_le hL
  have hxS : x ∈ Metric.sphere p L := by
    rw [Metric.mem_sphere, dist_comm]
    exact hx
  obtain ⟨_, hsource, _, hdist⟩ := hrel L hL
  obtain ⟨z, hz⟩ := hsource ⟨x, hxS⟩
  obtain ⟨j, hj, hnear⟩ := hN z
  have hyS : rayExtension (η j) L ∈ Metric.sphere p L := by
    rw [Metric.mem_sphere]
    simpa only [rayExtension_zero, sub_zero, abs_of_pos hLpos] using
      rayExtension_dist (η j) hLpos.le (le_refl 0)
  have hy : sphereLinkRelation hc L ((ε / 2) / 4)
      ⟨rayExtension (η j) L, hyS⟩ (asymptoticLinkProjection hc (η j)) := by
    refine ⟨η j, rfl, ?_⟩
    simpa only [dist_self, zero_div] using (show 0 < (ε / 2) / 4 by positivity)
  have herror := hdist ⟨x, hxS⟩ ⟨rayExtension (η j) L, hyS⟩ z
    (asymptoticLinkProjection hc (η j)) hz hy
  refine ⟨j, hj, ?_⟩
  have he := (abs_lt.mp herror).2
  change (g.edist x (rayExtension (η j) L)).toReal / L -
    dist z (asymptoticLinkProjection hc (η j)) < ε / 2 at he
  linarith

end PoincareConjecture.RiemannianMetric
