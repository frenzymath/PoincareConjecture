import PoincareConjecture.Definitions.M66
import PoincareConjecture.Statements.M61Width
import PoincareConjecture.Statements.M65
import PoincareConjecture.Statements.M58LoopSmoothing
























set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]


structure M66Predecessors {t₀ t₁ : ℝ}
    (hM61 : M61RawWidthCore.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    (P : M65RawFlowInput M t₀ t₁)
    (C : M66ClassData P) where
  width : ∀ t : Set.Icc t₀ t₁,
    M61FreeClassWidthProperties (P.flow.metric t.1) P.family
  deformation : ∀ {a b : ℝ} (Q : M65RawFlowInput M a b),
    Nonempty (M65Conclusion M Q
      (m65PredecessorsFromServices hM61 hM64 Q))
  short_loop : RepairedShortLoopTrivialityTheory.{u}



  short_loop_application : ∀ t : Set.Icc t₀ t₁, ∃ ζ : ℝ, 0 < ζ ∧
    ∀ source : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M)),
      (∀ c, IsNullHomotopicLoop (source c)) →
      (∀ c, freeLoopLength (P.flow.metric t.1) (source c) < ζ) →
        source.Homotopic (constantLoopFamily C.basepoint)



structure M66Conclusion {t₀ t₁ : ℝ}
    (hM61 : M61RawWidthCore.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    (P : M65RawFlowInput M t₀ t₁)
    (C : M66ClassData P)
    (H : M66Predecessors hM61 hM65 P C) where
  width_nonnegative : ∀ t : Set.Icc t₀ t₁, 0 ≤ m66Width P t
  forward_difference_bound : ∀ t : Set.Icc t₀ t₁,
    t.1 < t₁ → ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ s : Set.Icc t₀ t₁, t.1 < s.1 → s.1 < t.1 + delta →
        (m66Width P s - m66Width P t) / (s.1 - t.1) ≤
          -2 * Real.pi -
            flowScalarCurvatureInfimum P.flow t.1 / 2 * m66Width P t +
              epsilon
  continuous_at : ∀ t : Set.Icc t₀ t₁,
    ContinuousAt (fun s : Set.Icc t₀ t₁ => m66Width P s) t

set_option linter.style.haveILetI false


theorem m66PredecessorsFromServices
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁)
    (C : M66ClassData P) : M66Predecessors hM61 hM65 P C := by
  letI : T2Space M := P.hausdorff
  letI : SecondCountableTopology M := P.second_countable
  have short_loop_application : ∀ t : Set.Icc t₀ t₁, ∃ ζ : ℝ, 0 < ζ ∧
      ∀ source : ContinuousMap LoopTwoSphere
          (C1FreeLoopSpace (M := M)),
        (∀ c, IsNullHomotopicLoop (source c)) →
        (∀ c, freeLoopLength (P.flow.metric t.1) (source c) < ζ) →
          source.Homotopic (constantLoopFamily C.basepoint) := by
    intro t
    exact hM58.short_loop.raw_short_loop_family_trivial
      (P.flow.metric t.1) P.compact C.connected C.basepoint
      C.pi_two_subsingleton
  refine
    { width := fun t => hM61.free_class (P.flow.metric t.1) P.compact
        P.family P.family_null
      deformation := fun Q => hM65 M Q
      short_loop := hM58
      short_loop_application := short_loop_application }

def M66SmoothTimeTheory
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁)
    (C : M66ClassData P),
    Nonempty (M66Conclusion hM61 hM65 P C
      (m66PredecessorsFromServices hM61 hM58 hM65 P C))

end PoincareConjecture
