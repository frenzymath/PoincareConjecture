import PoincareConjecture.Proofs.M11.OrdinaryChartTransitions
import PoincareConjecture.Definitions.M11AdaptedAtlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def ordinaryBox (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval)
    (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) (p : M) :
    AdaptedMetricBox n (I.domain × M) (fun q ↦ q.1.val) I where
  interval := I
  spatial := spatialChartDomain p
  spatial_nonempty := ⟨chartAt (EuclideanSpace ℝ (Fin n)) p p, mem_chart_target _ p⟩
  interval_relatively_open := ⟨univ, isOpen_univ, by simp⟩
  toSpacetime q := (q.1, spatialChartInverse p q.2)
  openEmbedding := Topology.IsOpenEmbedding.id.prodMap (spatialChartInverse_openEmbedding p)
  time_toSpacetime := fun _ ↦ rfl
  metric := ordinaryChartMetric g p
  metric_smooth := ordinaryChartMetric_smooth g I.domain hg p
  metric_symm := fun t _ x _ v w ↦ ordinaryChartMetric_symm g p t x v w
  metric_pos := fun t _ x hx v hv ↦ ordinaryChartMetric_pos g p t x hx v hv

noncomputable def ordinaryTransition (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (p q : M) (t : ℝ) (ht : t ∈ I.domain)
    (x : spatialChartDomain (n := n) p) (y : spatialChartDomain (n := n) q)
    (hxy : spatialChartInverse p x = spatialChartInverse q y) :
    AdaptedMetricTransition (ordinaryBox g I hg p) (ordinaryBox g I hg q) t x.val y.val where
  interval := I
  interval_relatively_open := ⟨univ, isOpen_univ, by simp⟩
  interval_subset_left := Subset.rfl
  interval_subset_right := Subset.rfl
  time_mem := ht
  coordinateChange := spatialChartTransition p q
  source_subset := inter_subset_left
  target_subset := inter_subset_left
  source_mem := by
    refine ⟨x.property, ?_⟩
    change spatialChartInverse p x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).source
    rw [hxy]
    exact (chartAt (EuclideanSpace ℝ (Fin n)) q).map_target y.property
  map_marked := by
    change chartAt (EuclideanSpace ℝ (Fin n)) q (spatialChartInverse p x) = y.val
    rw [hxy]
    exact (chartAt (EuclideanSpace ℝ (Fin n)) q).right_inv y.property
  smooth := spatialChartTransition_smooth p q
  symm_smooth := spatialChartTransition_symm_smooth p q
  box_eq := by
    intro s hs z hz
    apply Prod.ext
    · rfl
    · exact (spatialChartTransition_inverse_eq p q z hz).symm
  metric_eq := fun s _ z hz v w ↦ ordinaryChartMetric_transition g p q s z hz v w

noncomputable def ordinaryAtlas [Nonempty M] (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    AdaptedMetricAtlas n (I.domain × M) where
  time q := q.1.val
  interval := I
  time_continuous := continuous_subtype_val.comp continuous_fst
  time_range := by
    ext t
    constructor
    · rintro ⟨p, rfl⟩
      exact p.1.property
    · intro ht
      exact ⟨(⟨t, ht⟩, Classical.choice ‹Nonempty M›), rfl⟩
  box_index := M
  box := ordinaryBox g I hg
  box_covers := by
    intro p
    refine ⟨p.2, (p.1, ⟨chartAt (EuclideanSpace ℝ (Fin n)) p.2 p.2,
      mem_chart_target _ p.2⟩), ?_⟩
    apply Prod.ext
    · rfl
    · exact (chartAt (EuclideanSpace ℝ (Fin n)) p.2).left_inv (mem_chart_source _ p.2)
  transitions := by
    intro p q t ht _ x y hxy
    exact ⟨ordinaryTransition g I hg p q t ht x y (congrArg Prod.snd hxy)⟩

end PoincareConjecture.Proofs.M11
