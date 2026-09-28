import PoincareConjecture.Definitions.M25NeckCapTopology










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M]
  {g : RiemannianMetric 3 M} {H : ConnectedNeckCapCover g}



theorem RepairedNeckCapTopologyData.globalConclusion
    (D : RepairedNeckCapTopologyData g H) (hwhole : H.isWhole) :
    Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant) := by
  change H.X = Set.univ at hwhole
  rcases D with ⟨region, compatible⟩
  cases region with
  | twoCaps kind cap₁ cap₂ component union_eq contains_X =>
    rcases compatible with ⟨hε₁, hε₂, hC₁, hC₂⟩
    refine ⟨.closed _ kind component ?_ (.twoCaps cap₁ cap₂ union_eq hε₁ hε₂ hC₁ hC₂)⟩
    simpa only [hwhole] using contains_X
  | doubleCappedTube certificate kind component contains_X =>
    rcases compatible with ⟨hε₁, hε₂, hεt, hC₁, hC₂⟩
    refine ⟨.closed _ kind component ?_
      (.doubleCappedTube certificate rfl hε₁ hε₂ hεt hC₁ hC₂)⟩
    simpa only [hwhole] using contains_X
  | singleCap cap contains_X =>
    rcases compatible with ⟨hε, hC⟩
    refine ⟨.noncompact ⟨cap.carrier, Or.inl ⟨cap, rfl, hε, hC, ?_⟩, ?_⟩⟩
    · cases cap.model_kind <;> simp
    · simpa only [hwhole] using contains_X
  | cappedTube certificate contains_X =>
    rcases compatible with ⟨hεc, hεt, hC, _⟩
    refine ⟨.noncompact ⟨certificate.carrier,
      Or.inr ⟨certificate, rfl, hεc, hεt, hC, ?_⟩, ?_⟩⟩
    · cases certificate.cap.model_kind <;> simp
    · simpa only [hwhole] using contains_X
  | tube tube =>
    have hcontains : Set.univ ⊆ tube.carrier := by
      simpa only [hwhole] using tube.contains_X
    exact ⟨.tube { tube with contains_X := hcontains } compatible
      (Set.eq_univ_of_univ_subset hcontains)⟩
  | fibration fibration =>
    rcases compatible with ⟨hε, hcontains⟩
    have hwhole' : Set.univ ⊆ fibration.carrier := by
      simpa only [hwhole] using hcontains
    exact ⟨.fibration { fibration with contains_X := hwhole' } hε
      (Set.eq_univ_of_univ_subset hwhole')⟩



theorem appendixA25_of_appendixA21 (hlocal : AppendixA21Theory g H)
    (hwhole : H.isWhole) : AppendixA25Theory g H hwhole := by
  obtain ⟨region, compatible⟩ := hlocal
  exact (RepairedNeckCapTopologyData.mk region compatible).globalConclusion hwhole

end PoincareConjecture
