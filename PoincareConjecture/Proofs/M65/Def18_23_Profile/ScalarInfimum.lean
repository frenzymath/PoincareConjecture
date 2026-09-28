import PoincareConjecture.Proofs.M65.Def18_23_Profile.AreaComparisonProfile
import PoincareConjecture.Proofs.M04.ScalarEvolution










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁))




theorem flowScalarCurvatureInfimum_continuousOn
    (compact : IsCompact (Set.univ : Set M)) :
    ContinuousOn (flowScalarCurvatureInfimum F) (Set.Icc t₀ t₁) := by
  have hregular : ContinuousOn
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2)
      (Set.Icc t₀ t₁ ×ˢ Set.univ) :=
    F.contMDiffOn_scalarCurvature.continuousOn
  have hscalar : Continuous (fun p : Set.Icc t₀ t₁ × M =>
      (F.connection p.1.1).scalarCurvature p.2) :=
    hregular.comp_continuous (f := fun p : Set.Icc t₀ t₁ × M => (p.1.1, p.2))
      (continuous_subtype_val.prodMap continuous_id)
      (fun p => ⟨p.1.2, Set.mem_univ _⟩)
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : Set.Icc t₀ t₁ =>
    sInf (Set.range (fun x : M => (F.connection t.1).scalarCurvature x)))
  simpa only [Set.image_univ] using
    compact.continuous_sInf (f := fun t : Set.Icc t₀ t₁ =>
      fun x : M => (F.connection t.1).scalarCurvature x) hscalar



theorem flowScalarCurvatureInfimum_intervalIntegrable
    (compact : IsCompact (Set.univ : Set M))
    {s t : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (ht : t ∈ Set.Icc t₀ t₁) :
    IntervalIntegrable (fun v => flowScalarCurvatureInfimum F v / 2)
      MeasureTheory.volume s t :=
  (((flowScalarCurvatureInfimum_continuousOn F compact).div_const 2).mono
    (Set.uIcc_subset_Icc hs ht)).intervalIntegrable

end PoincareConjecture
