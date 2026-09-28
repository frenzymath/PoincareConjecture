import PoincareConjecture.Statements.M25NeckCapTopology











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

theorem repaired_a21_data
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M]
    (N : RepairedNeckCapTopologyTheory.{u})
    (g : RiemannianMetric 3 M) (H : ConnectedNeckCapCover g)
    (hε : H.epsilon ≤ N.epsilon₀) :
    Nonempty (RepairedNeckCapTopologyData g H) :=
  N.a21 g H hε

theorem repaired_a21_twoCaps
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} {H : ConnectedNeckCapCover g}
    (R : RepairedNeckCapTopologyData g H)
    {kind : ClosedComponentKind} {Y : Set M}
    (cap₁ cap₂ : CapCertificate g)
    (C : ClosedComponentCertificate kind Y)
    (hunion : Y = cap₁.carrier ∪ cap₂.carrier) (hX : H.X ⊆ Y)
    (_hregion : R.region = .twoCaps kind cap₁ cap₂ C hunion hX) :
    Nonempty (ClosedComponentCertificate kind Y) ∧ H.X ⊆ Y := by
  exact ⟨⟨C⟩, hX⟩

theorem repaired_a21_doubleCappedTube
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} {H : ConnectedNeckCapCover g}
    (R : RepairedNeckCapTopologyData g H)
    {kind : ClosedComponentKind}
    (tube : DoubleCappedTubeCertificate g)
    (C : ClosedComponentCertificate kind tube.carrier) (hX : H.X ⊆ tube.carrier)
    (_hregion : R.region = .doubleCappedTube tube kind C hX) :
    Nonempty (ClosedComponentCertificate kind tube.carrier) ∧
      H.X ⊆ tube.carrier := by
  exact ⟨⟨C⟩, hX⟩






theorem repaired_a21_region_cases
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} {H : ConnectedNeckCapCover g}
    (R : RepairedNeckCapTopologyData g H) :
    (∃ kind : ClosedComponentKind, ∃ Y : Set M,
      ∃ cap₁ cap₂ : CapCertificate g,
      ∃ C : ClosedComponentCertificate kind Y,
      ∃ hunion : Y = cap₁.carrier ∪ cap₂.carrier,
      ∃ hX : H.X ⊆ Y,
        R.region = .twoCaps kind cap₁ cap₂ C hunion hX) ∨
    (∃ tube : DoubleCappedTubeCertificate g,
      ∃ kind : ClosedComponentKind,
      ∃ C : ClosedComponentCertificate kind tube.carrier,
      ∃ hX : H.X ⊆ tube.carrier,
        R.region = .doubleCappedTube tube kind C hX) ∨
    (∃ cap : CapCertificate g, ∃ hX : H.X ⊆ cap.carrier,
      R.region = .singleCap cap hX) ∨
    (∃ tube : CappedTubeCertificate g, ∃ hX : H.X ⊆ tube.carrier,
      R.region = .cappedTube tube hX) ∨
    (∃ tube : EpsilonTubeCertificate g H.X,
      R.region = .tube tube) ∨
    (∃ fibration : SphereBundleCircleCertificate g H.X,
      R.region = .fibration fibration) := by
  cases h : R.region with
  | twoCaps kind cap₁ cap₂ C hunion hX =>
      exact Or.inl ⟨kind, _, cap₁, cap₂, C, hunion, hX, rfl⟩
  | doubleCappedTube tube kind C hX =>
      exact Or.inr (Or.inl ⟨tube, kind, C, hX, rfl⟩)
  | singleCap cap hX =>
      exact Or.inr (Or.inr (Or.inl ⟨cap, hX, rfl⟩))
  | cappedTube tube hX =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨tube, hX, rfl⟩)))
  | tube tube =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨tube, rfl⟩))))
  | fibration fibration =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨fibration, rfl⟩))))

end PoincareConjecture.M38
