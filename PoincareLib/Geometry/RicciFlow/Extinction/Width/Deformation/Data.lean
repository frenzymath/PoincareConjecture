import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Based
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Deformation.Family

/-!
# M65 primitive loop-family contract

The input is the raw continuous family in Morgan--Tian Proposition 18.24.
Its class is carried by an actual continuous-map homotopy witness rather than
by a fabricated sphere certificate.  The output uses the same raw family and
Ricci-flow slab, and an actual time-indexed family of regular loop families.

Source: Morgan--Tian Proposition 18.24, Claims 19.23 and 19.25--19.32,
pp. 433--434 and 453--464, with the corrected Section 19.2 estimates.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareMT

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

end PoincareMT
