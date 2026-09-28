import PoincareConjecture.Definitions.M61Width
import PoincareConjecture.Definitions.Ch18.Deformation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure M65RawFlowInput (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (t₀ t₁ : ℝ) where
  time_ordered : t₀ ≤ t₁
  flow : RicciFlow 3 M (Set.Icc t₀ t₁)
  compact : IsCompact (Set.univ : Set M)
  hausdorff : T2Space M
  second_countable : SecondCountableTopology M
  family : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))
  family_null : M61NullFamily family

structure M65DeformedFamily (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁) (zeta : ℝ) where
  family : Set.Icc t₀ t₁ →
    ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))
  family_continuous : Continuous (fun p : Set.Icc t₀ t₁ × LoopTwoSphere =>
    (family p.1) p.2)
  null : ∀ t, M61NullFamily (family t)
  free_homotopy_to_initial : ∀ t, P.family.Homotopic (family t)
  initial_area_close : ∀ c,
    |fillingArea (P.flow.metric t₀)
        ((family ⟨t₀, ⟨le_rfl, P.time_ordered⟩⟩) c) -
      fillingArea (P.flow.metric t₀) (P.family c)| < zeta
  terminal_alternative : ∀ c,
    freeLoopLength (P.flow.metric t₁)
        ((family ⟨t₁, ⟨P.time_ordered, le_rfl⟩⟩) c) < zeta ∨
      fillingArea (P.flow.metric t₁)
          ((family ⟨t₁, ⟨P.time_ordered, le_rfl⟩⟩) c) ≤
        areaComparisonProfile P.flow
          (fillingArea (P.flow.metric t₀)
            ((family ⟨t₀, ⟨le_rfl, P.time_ordered⟩⟩) c)) t₁ + zeta

end PoincareConjecture
