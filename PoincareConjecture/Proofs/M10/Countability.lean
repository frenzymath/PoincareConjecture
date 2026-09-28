import PoincareConjecture.Proofs.M10.MinimizingLifts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem secondCountableTopology_of_exponential
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) : SecondCountableTopology M := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨(F.metric T).inner, (F.metric T).toContinuousRiemannianMetric.continuous,
      fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  have hcont : Continuous (fun Z : TangentSpace (𝓡 n) p ↦ G.gamma Z τ) := by
    apply continuous_iff_continuousAt.mpr
    intro Z
    exact (G.gamma_smooth.continuousOn.continuousAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ Z, hτ, hmax⟩)).comp
      (continuous_id.prodMk continuous_const).continuousAt
  have hsurj : Function.Surjective (fun Z : TangentSpace (𝓡 n) p ↦ G.gamma Z τ) := by
    intro q
    obtain ⟨Z, hZ, _⟩ := exists_minimizing_lift hL G q τ hτ hmax
    exact ⟨Z, hZ⟩
  let : TopologicalSpace.SeparableSpace M := hsurj.denseRange.separableSpace hcont
  exact UniformSpace.secondCountable_of_separable M

end PoincareConjecture.M10
