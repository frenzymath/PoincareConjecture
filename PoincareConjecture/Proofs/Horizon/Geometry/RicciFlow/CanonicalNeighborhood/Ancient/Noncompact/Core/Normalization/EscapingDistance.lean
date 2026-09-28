import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Normalization.Soul
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.EscapingScale

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)] [∀ k, ConnectedSpace (M k)]

theorem nonround_curvature_scale_distance_tendsto_atTop_of_services
    (P : NoncompactKappaServices.{u})
    (K : ∀ k, AncientKappaSolution 3 (M k)) (p q : ∀ k, M k)
    (hnonround : ∀ k, ¬ IsRoundAncientKappaSolution (K k))
    (hnormalized : ∀ k, ((K k).flow.connection 0).scalarCurvature (p k) = 1)
    (hescape : Tendsto (fun k => (((K k).flow.metric 0).edist (q k) (p k)).toReal)
      atTop atTop) :
    Tendsto (fun k => Real.sqrt (((K k).flow.connection 0).scalarCurvature (q k)) *
      (((K k).flow.metric 0).edist (q k) (p k)).toReal) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  obtain ⟨L, _, hL⟩ := nonround_uniform_curvature_scale_separation_of_services P
    (A := max 0 A) (le_max_left _ _)
  filter_upwards [(tendsto_atTop.1 hescape) (L + 1)] with k hk
  exact (le_max_right 0 A).trans
    (hL (K k) (p k) (q k) (hnonround k) (hnormalized k) (by linarith)).le

theorem nonround_curvature_scale_distance_tendsto_atTop
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : ∀ k, AncientKappaSolution 3 (M k)) (p q : ∀ k, M k)
    (hnonround : ∀ k, ¬ IsRoundAncientKappaSolution (K k))
    (hnormalized : ∀ k, ((K k).flow.connection 0).scalarCurvature (p k) = 1)
    (hescape : Tendsto (fun k => (((K k).flow.metric 0).edist (q k) (p k)).toReal)
      atTop atTop) :
    Tendsto (fun k => Real.sqrt (((K k).flow.connection 0).scalarCurvature (q k)) *
      (((K k).flow.metric 0).edist (q k) (p k)).toReal) atTop atTop := by
  exact nonround_curvature_scale_distance_tendsto_atTop_of_services P.noncompactServices K p q hnonround hnormalized hescape

theorem nonround_normalized_distance_tendsto_atTop_of_services
    (P : NoncompactKappaServices.{u})
    (K : ∀ k, AncientKappaSolution 3 (M k)) (p q : ∀ k, M k)
    (N : ∀ k, AncientKappaNormalization (K k) (q k) 0)
    (hnonround : ∀ k, ¬ IsRoundAncientKappaSolution (K k))
    (hnormalized : ∀ k, ((K k).flow.connection 0).scalarCurvature (p k) = 1)
    (hescape : Tendsto (fun k => (((K k).flow.metric 0).edist (q k) (p k)).toReal)
      atTop atTop) :
    Tendsto (fun k => (((N k).target.flow.metric 0).edist (q k) (p k)).toReal)
      atTop atTop := by
  simpa only [AncientKappaNormalization.toReal_edist_zero,
    AncientKappaNormalization.scale_eq] using
    nonround_curvature_scale_distance_tendsto_atTop_of_services P K p q hnonround hnormalized hescape

theorem nonround_normalized_distance_tendsto_atTop
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : ∀ k, AncientKappaSolution 3 (M k)) (p q : ∀ k, M k)
    (N : ∀ k, AncientKappaNormalization (K k) (q k) 0)
    (hnonround : ∀ k, ¬ IsRoundAncientKappaSolution (K k))
    (hnormalized : ∀ k, ((K k).flow.connection 0).scalarCurvature (p k) = 1)
    (hescape : Tendsto (fun k => (((K k).flow.metric 0).edist (q k) (p k)).toReal)
      atTop atTop) :
    Tendsto (fun k => (((N k).target.flow.metric 0).edist (q k) (p k)).toReal)
      atTop atTop := by
  exact nonround_normalized_distance_tendsto_atTop_of_services P.noncompactServices K p q N hnonround hnormalized hescape

theorem nonround_normalized_soul_distance_tendsto_atTop_of_services
    (P : NoncompactKappaServices.{u})
    (K : ∀ k, AncientKappaSolution 3 (M k)) (q : ∀ k, M k)
    (N : ∀ k, AncientKappaNormalization (K k) (q k) 0)
    (soul : ∀ k, RiemannianMetric.PointSoulData ((K k).flow.metric 0))
    (hnonround : ∀ k, ¬ IsRoundAncientKappaSolution (K k))
    (hnormalized : ∀ k,
      ((K k).flow.connection 0).scalarCurvature (soul k).center = 1)
    (hescape : Tendsto
      (fun k => (((K k).flow.metric 0).edist (q k) (soul k).center).toReal)
      atTop atTop) :
    Tendsto (fun k => (((N k).target.flow.metric 0).edist
      (q k) ((N k).pointSoul (soul k)).center).toReal) atTop atTop :=
  nonround_normalized_distance_tendsto_atTop_of_services P K (fun k => (soul k).center) q N
    hnonround hnormalized hescape

theorem nonround_normalized_soul_distance_tendsto_atTop
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (K : ∀ k, AncientKappaSolution 3 (M k)) (q : ∀ k, M k)
    (N : ∀ k, AncientKappaNormalization (K k) (q k) 0)
    (soul : ∀ k, RiemannianMetric.PointSoulData ((K k).flow.metric 0))
    (hnonround : ∀ k, ¬ IsRoundAncientKappaSolution (K k))
    (hnormalized : ∀ k,
      ((K k).flow.connection 0).scalarCurvature (soul k).center = 1)
    (hescape : Tendsto
      (fun k => (((K k).flow.metric 0).edist (q k) (soul k).center).toReal)
      atTop atTop) :
    Tendsto (fun k => (((N k).target.flow.metric 0).edist
      (q k) ((N k).pointSoul (soul k)).center).toReal) atTop atTop := by
  exact nonround_normalized_soul_distance_tendsto_atTop_of_services P.noncompactServices K q N soul hnonround hnormalized hescape

end PoincareConjecture
