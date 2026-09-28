import PoincareConjecture.Proofs.M14.Sec6_3_InitialExistence
import PoincareConjecture.Proofs.M14.Sec6_3_MaximalDomain

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem exists_gauge_squareClock_interval (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (hprev : ∃ a ∈ (G.gaugeCover.interval b).domain, a < t₀.val) :
    ∃ smax : ℝ, 0 < smax ∧
      ∀ s ∈ Icc 0 smax, t₀.val - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
  obtain ⟨a, ha, hat⟩ := hprev
  refine ⟨Real.sqrt (t₀.val - a), Real.sqrt_pos.mpr (sub_pos.mpr hat), ?_⟩
  intro s hs
  apply (G.gaugeCover.interval b).ordConnected.out ha t₀.property
  have hsq := (sq_le_sq₀ hs.1 (Real.sqrt_nonneg (t₀.val - a))).mpr hs.2
  rw [Real.sq_sqrt (sub_nonneg.mpr hat.le)] at hsq
  exact ⟨by linarith, sub_le_self _ (sq_nonneg s)⟩

theorem initialValueDomain_initial_tube_in_gauge
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {smax : ℝ} (hsmax : 0 < smax)
    (htime : ∀ s ∈ Icc 0 smax, t₀.val - s ^ 2 ∈ (G.gaugeCover.interval b).domain) :
    ∃ c : ℝ, 0 < c ∧ c ≤ smax ∧
      ∃ U : Set (G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀))),
        IsOpen U ∧ Z ∈ U ∧ U ×ˢ Icc 0 c ⊆
          initialValueDomain G t₀.val ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) := by
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  obtain ⟨c, hc, hcmax, U, hU, hZU, hpath⟩ :=
    exists_localInitialValuePath_neighborhood_in_gauge hM04 hM12 b W t₀ x₀ Z hsmax htime
  refine ⟨c, hc, hcmax, U, hU, hZU, ?_⟩
  intro z hz
  exact initialValueDomain_prefix
    ((initialValueDomain_positive_iff hc).mpr (hpath z.1 hz.1)) hz.2.1 hz.2.2

theorem initialValueDomain_zero_relative_open_in_gauge
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    (hprev : ∃ a ∈ (G.gaugeCover.interval b).domain, a < t₀.val) :
    ∃ U : Set (G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) × ℝ),
      IsOpen U ∧ (Z, 0) ∈ U ∧
        U ∩ M14AdmissibleParameter G t₀.val
          ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) ⊆
          initialValueDomain G t₀.val ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) := by
  obtain ⟨smax, hsmax, htime⟩ := exists_gauge_squareClock_interval b t₀ hprev
  obtain ⟨c, hc, _, U, hU, hZU, htube⟩ :=
    initialValueDomain_initial_tube_in_gauge hM04 hM12 b t₀ x₀ Z hsmax htime
  refine ⟨U ×ˢ Iio c, hU.prod isOpen_Iio, ⟨hZU, hc⟩, ?_⟩
  intro z hz
  exact htube ⟨hz.1.1, hz.2.1, hz.1.2.le⟩

end PoincareConjecture.M14
