import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparationLabels
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import PoincareConjecture.Definitions.M25NeckCapTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem NeckOnlyCover.exists_uniform_nonseparating_center_labels :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      (∃ N ∈ H.necks, N.center ∈ H.X ∧ N.IsNonseparating) →
      ∀ N ∈ H.necks, N.center ∈ H.X → N.IsNonseparating := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hlabel⟩ :=
    NeckOnlyCover.exists_locally_constant_separation_label.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hH hsource
  obtain ⟨label, hlabel⟩ := hlabel H hH
  let : PreconnectedSpace H.X :=
    Subtype.preconnectedSpace H.connected_X.isPreconnected
  obtain ⟨N0, hN0, hN0X, hN0non⟩ := hsource
  have hN0not : ¬ N0.IsSeparating := by
    intro hsep
    exact (N0.m25_isSeparating_iff_not_isNonseparating.mp hsep) hN0non
  have hN0label : label ⟨N0.center, hN0X⟩ ≠ true := by
    intro htrue
    exact hN0not ((hlabel N0 hN0 hN0X).mp htrue)
  intro N hN hNX
  have hNnot : ¬ N.IsSeparating := by
    intro hsep
    apply hN0label
    exact
      (label.apply_eq_of_preconnectedSpace
        ⟨N0.center, hN0X⟩ ⟨N.center, hNX⟩).trans
        ((hlabel N hN hNX).mpr hsep)
  by_contra hnon
  exact hNnot ((N.m25_isSeparating_iff_not_isNonseparating.mpr hnon))

end PoincareConjecture
