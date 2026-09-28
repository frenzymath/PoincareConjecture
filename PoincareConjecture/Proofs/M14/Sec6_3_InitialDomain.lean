import PoincareConjecture.Proofs.M14.Sec6_3_GaugeTimeDirection
import PoincareConjecture.Proofs.M14.Sec6_3_InitialNeighborhood

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem initialValueDomain_initial_tube
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) (hprev : ∃ a ∈ I.domain, a < T)
    (Z : G.Horizontal x) :
    ∃ c : ℝ, 0 < c ∧ ∃ U : Set (G.Horizontal x),
      IsOpen U ∧ Z ∈ U ∧ U ×ˢ Icc 0 c ⊆ initialValueDomain G T x := by
  obtain ⟨b, ⟨t₀, x₀⟩, rfl⟩ := G.gaugeCover.covers x
  have ht₀ : t₀.val = T := ((G.gaugeCover.cylinder b).time_eq (t₀, x₀)).symm.trans hbase
  have hprev' : ∃ a ∈ I.domain, a < t₀.val := by simpa only [ht₀] using hprev
  obtain ⟨smax, hsmax, htime⟩ :=
    exists_gauge_squareClock_interval b t₀ (gauge_has_earlier_time b t₀ x₀ hprev')
  obtain ⟨c, hc, _, U, hU, hZU, htube⟩ :=
    initialValueDomain_initial_tube_in_gauge hM04 hM12 b t₀ x₀ Z hsmax htime
  exact ⟨c, hc, U, hU, hZU, ht₀ ▸ htube⟩

theorem initialValueDomain_zero_relative_open
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) (Z : G.Horizontal x) :
    ∃ U : Set (G.Horizontal x × ℝ), IsOpen U ∧ (Z, 0) ∈ U ∧
      U ∩ M14AdmissibleParameter G T x ⊆ initialValueDomain G T x := by
  by_cases hprev : ∃ a ∈ I.domain, a < T
  · obtain ⟨c, hc, U, hU, hZU, htube⟩ :=
      initialValueDomain_initial_tube hM04 hM12 hbase hprev Z
    refine ⟨U ×ˢ Iio c, hU.prod isOpen_Iio, ⟨hZU, hc⟩, ?_⟩
    intro z hz
    exact htube ⟨hz.1.1, hz.2.1, hz.1.2.le⟩
  · refine ⟨univ, isOpen_univ, mem_univ _, ?_⟩
    intro z hz
    have hnonneg : T ≤ T - z.2 ^ 2 :=
      le_of_not_gt (fun hlt => hprev ⟨T - z.2 ^ 2, hz.2.2, hlt⟩)
    exact Or.inl (sq_eq_zero_iff.mp (le_antisymm (by linarith) (sq_nonneg z.2)))

end PoincareConjecture.M14
