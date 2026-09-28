import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.Comparison

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral
universe u
namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

def m66RestrictInput {a b : ℝ} (P : M65RawFlowInput M a b)
    (t s : Set.Icc a b) (hts : t.1 < s.1) : M65RawFlowInput M t.1 s.1 where
  time_ordered := hts.le
  flow := {
    metric := P.flow.metric
    connection := P.flow.connection
    interval := Set.ordConnected_Icc
    nontrivial := ⟨t, ⟨le_rfl, hts.le⟩, s, ⟨hts.le, le_rfl⟩, ne_of_lt hts⟩
    smooth := P.flow.smooth.mono (Set.prod_mono (Set.Icc_subset_Icc t.2.1 s.2.2)
      (Set.Subset.refl _))
    equation := fun v hv x u w =>
      (P.flow.equation v ⟨t.2.1.trans hv.1, hv.2.trans s.2.2⟩ x u w).mono
        (Set.Icc_subset_Icc t.2.1 s.2.2) }
  compact := P.compact
  hausdorff := P.hausdorff
  second_countable := P.second_countable
  family := P.family
  family_null := P.family_null

theorem m66_subslab_comparison
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    {a b : ℝ} (P : M65RawFlowInput M a b) (C : M66ClassData P)
    (t s : Set.Icc a b) (hts : t.1 < s.1) :
    m66Width P s ≤
      Real.exp (-(∫ v in t.1..s.1, flowScalarCurvatureInfimum P.flow v / 2)) *
        (m66Width P t - 2 * Real.pi *
          (∫ v in t.1..s.1, Real.exp
            (∫ x in t.1..v, flowScalarCurvatureInfimum P.flow x / 2))) :=
  m66_endpoint_comparison hM61 hM58 hM65
    (m66RestrictInput P t s hts) C.connected C.basepoint
    C.pi_two_subsingleton C.raw_nontrivial

end PoincareConjecture
