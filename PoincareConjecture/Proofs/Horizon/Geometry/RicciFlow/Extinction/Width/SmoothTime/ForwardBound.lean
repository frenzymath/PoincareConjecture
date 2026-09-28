import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.Analysis.Profile








set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral
universe u
namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]


theorem m66_forward_difference_bound
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    {a b : ℝ} (P : M65RawFlowInput M a b) (C : M66ClassData P)
    (t : Set.Icc a b) (_ht : t.1 < b)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ s : Set.Icc a b, t.1 < s.1 → s.1 < t.1 + delta →
        (m66Width P s - m66Width P t) / (s.1 - t.1) ≤
          -2 * Real.pi -
            flowScalarCurvatureInfimum P.flow t.1 / 2 * m66Width P t + epsilon := by
  have hr : ContinuousOn (flowScalarCurvatureInfimum P.flow) (Set.Icc a b) :=
    continuousOn_iff_continuous_domRestrict.mpr C.scalar_infimum_continuous
  obtain ⟨delta, hdelta, hprofile⟩ := smoothWidthProfile_forward_bound
    (w := m66Width P t) t.2.2
    (hr.mono (Set.Icc_subset_Icc t.2.1 le_rfl)) hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro s hts hsdelta
  have hcomp := m66_subslab_comparison hM61 hM58 hM65 P C t s hts
  change m66Width P s ≤ smoothWidthProfile
    (flowScalarCurvatureInfimum P.flow) t.1 (m66Width P t) s.1 at hcomp
  exact (div_le_div_of_nonneg_right (sub_le_sub_right hcomp _) (sub_pos.mpr hts).le).trans
    (hprofile s.1 ⟨hts.le, s.2.2⟩ hts hsdelta)

end PoincareConjecture
