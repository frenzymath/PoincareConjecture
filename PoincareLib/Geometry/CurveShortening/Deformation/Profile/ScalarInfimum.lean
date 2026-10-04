import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.Profile.AreaComparisonProfile
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within

/-!
# Continuity of the scalar-curvature infimum on the flow slab

Compactness and joint scalar-curvature regularity justify the coefficient
in Definition 18.23 and Claim 18.26, Morgan--Tian pp. 433-434. Only the
closed lower scalar-regularity theorem and Mathlib's compact infimum theorem
are used; no regularity outside the actual time domain is asserted.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {t₀ t₁ : ℝ} (F : RicciFlow 3 M (Set.Icc t₀ t₁))

/-- The minimum scalar coefficient in Definition 18.23, p. 433, is
continuous on the closed time slab of a compact flow. For an empty manifold
Mathlib's real infimum convention gives the same continuity statement. -/
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

/-- The coefficient of the ODE in Definition 18.23 is integrable on any
included subslab, in either orientation. Source: Morgan--Tian p. 433. -/
theorem flowScalarCurvatureInfimum_intervalIntegrable
    (compact : IsCompact (Set.univ : Set M))
    {s t : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (ht : t ∈ Set.Icc t₀ t₁) :
    IntervalIntegrable (fun v => flowScalarCurvatureInfimum F v / 2)
      MeasureTheory.volume s t :=
  (((flowScalarCurvatureInfimum_continuousOn F compact).div_const 2).mono
    (Set.uIcc_subset_Icc hs ht)).intervalIntegrable

end PoincareMT
