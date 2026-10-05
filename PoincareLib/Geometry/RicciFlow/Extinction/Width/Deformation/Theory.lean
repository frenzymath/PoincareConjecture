import PoincareLib.Geometry.RicciFlow.Extinction.Width.Deformation.Data
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Theory
import PoincareLib.Geometry.CurveShortening.Comparison.Theory

/-!
# M65 loop-family deformation

Natural-language theorem statement: given a compact smooth three-manifold
Ricci-flow slab and a raw continuous sphere family of null C1 loops, choose
the M61 family-width data and the complete M64 comparison output on this flow.
For each positive `zeta`, construct a concrete time-indexed family of raw loop
families. It is jointly continuous, null in every member, preserves the
displayed family's continuous-map homotopy class, changes every initial
filling area by less than `zeta`, and at terminal time each loop is either
shorter than `zeta` or satisfies the Morgan--Tian integrating-factor area
bound. The profile is the canonical `areaComparisonProfile` from the
deformation definitions. The source records the initial equality in based
`pi_3`; this contract records its raw free-loop reformulation, to be related
to the based class by the preceding `pi_2`-trivial identification.

The source is Proposition 18.24 and Claims 19.23, 19.25--19.32,
Morgan--Tian 2007, pp. 433--434 and 453--464, with the 2015 Section 19.2
correction.  The exact M64 approximation and M61 width services are explicit
predecessors; they are not re-proved or represented by arbitrary `Prop`
labels.  Definitions contain no admission.  The single theorem-owned
admission is in `Proofs/M65.lean`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure M65Predecessors (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁) where
  width : M61FamilyWidthProperties (P.flow.metric t₀) P.family
  m64 : M64ThreeDimensionalFlowConclusion P.flow

structure M65Conclusion (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁)
    (H : M65Predecessors M P) where
  deformation : ∀ zeta : ℝ, 0 < zeta →
    Nonempty (M65DeformedFamily M P zeta)

noncomputable def m65PredecessorsFromServices
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁) :
    M65Predecessors M P := by
  letI : T2Space M := P.hausdorff
  letI : SecondCountableTopology M := P.second_countable
  let A : M64ThreeDimensionalFlowConclusion P.flow :=
    Classical.choice (hM64.2.2.2 M t₀ t₁ P.flow P.compact)
  refine
    { width := hM61.family (P.flow.metric t₀) P.compact P.family P.family_null
      m64 := A }

def M65DeformationTheory
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u}) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {t₀ t₁ : ℝ} (P : M65RawFlowInput M t₀ t₁),
    Nonempty (M65Conclusion M P (m65PredecessorsFromServices hM61 hM64 P))

end PoincareMT
