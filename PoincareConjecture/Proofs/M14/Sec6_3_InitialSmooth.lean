import PoincareConjecture.Proofs.M14.Sec6_3_InitialFamily
import PoincareConjecture.Proofs.M14.Sec6_3_InitialDomain

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

theorem initialValueCurve_smooth_initial_tube
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) (hprev : ∃ a ∈ I.domain, a < T)
    (Z : G.Horizontal x) :
    ∃ d : ℝ, 0 < d ∧ ∃ U : Set (G.Horizontal x), IsOpen U ∧ Z ∈ U ∧
      U ×ˢ Icc 0 d ⊆ initialValueDomain G T x ∧
      M14HorizontalFamilySmooth G (initialValueCurve G T x) (U ×ˢ Icc 0 d) := by
  obtain ⟨b, ⟨t₀, x₀⟩, rfl⟩ := G.gaugeCover.covers x
  have ht₀ : t₀.val = T := ((G.gaugeCover.cylinder b).time_eq (t₀, x₀)).symm.trans hbase
  have hprev' : ∃ a ∈ I.domain, a < t₀.val := by simpa only [ht₀] using hprev
  obtain ⟨smax, hsmax, htime⟩ :=
    exists_gauge_squareClock_interval b t₀ (gauge_has_earlier_time b t₀ x₀ hprev')
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  obtain ⟨d, hd, _, U, hU, hZU, htube, hsm⟩ :=
    initialValueCurve_smooth_initial_tube_in_gauge hM04 hM12 b W t₀ x₀ Z hsmax htime
  exact ⟨d, hd, U, hU, hZU, ht₀ ▸ htube, ht₀ ▸ hsm⟩

theorem initialValueCurve_smooth_of_no_earlier_time
    (hbase : G.spacetime.timeFunction x = T) (hprev : ¬ ∃ a ∈ I.domain, a < T) :
    M14HorizontalFamilySmooth G (initialValueCurve G T x) (initialValueDomain G T x) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨metric⟩
  apply (contMDiffOn_const (c := x)).congr
  intro z hz
  have ha := initialValueDomain_admissible hbase hz
  have hle : T ≤ T - z.2 ^ 2 := le_of_not_gt (fun hlt => hprev ⟨_, ha.2, hlt⟩)
  have hs : z.2 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith) (sq_nonneg z.2))
  rw [hs, initialValueCurve_zero]

theorem initialValueCurve_contMDiffWithinAt_zero
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) (Z : G.Horizontal x) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    ContMDiffWithinAt ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z => initialValueCurve G T x z.1 z.2) (initialValueDomain G T x) (Z, 0) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨metric⟩
  by_cases hprev : ∃ a ∈ I.domain, a < T
  · obtain ⟨d, hd, U, hU, hZU, _, hsm⟩ :=
      initialValueCurve_smooth_initial_tube hM04 hM12 hbase hprev Z
    have hnear : U ×ˢ Icc 0 d ∈ 𝓝[initialValueDomain G T x] (Z, (0 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        ((hU.prod isOpen_Iio).mem_nhds (show (Z, (0 : ℝ)) ∈ U ×ˢ Iio d from ⟨hZU, hd⟩))]
        with w hw hUw
      exact ⟨hUw.1, initialValueDomain_nonneg hw, hUw.2.le⟩
    exact (hsm (Z, 0) ⟨hZU, le_rfl, hd.le⟩).mono_of_mem_nhdsWithin hnear
  · exact initialValueCurve_smooth_of_no_earlier_time hbase hprev (Z, 0) (initialValueDomain_zero Z)

end PoincareConjecture.M14
