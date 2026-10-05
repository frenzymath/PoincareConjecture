import PoincareLib.Geometry.CurveShortening.Comparison.FamilyAdapters
import PoincareLib.Geometry.CurveShortening.Deformation.Analysis.Energy.BadTimes

/-!
# Energy good times for the exact M64 family

Equation (19.9) and the bad-time estimate on printed p. 455 of
Morgan--Tian. The common constant is the checked M64 energy bound on the
displayed family, with the original ambient geometry and approximation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral
open MeasureTheory

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta : ℝ}

/-- The literal spatial curvature energy in Equation (19.9), p. 455. -/
noncomputable def m65FamilyEnergy (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod,
    m62CurvatureSquared (G.product circumference h).flow
      ((C.solutions circumference h).curve z) t x *
      curveSpeed (G.product circumference h).flow
        ((C.solutions circumference h).curve z) t x

/-- The energy in Equation (19.9), p. 455, is nonnegative since both its
curvature self-pairing and speed density are nonnegative. -/
theorem m65FamilyEnergy_nonneg (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) (t : ℝ) :
    0 ≤ m65FamilyEnergy C circumference h z t := by
  apply intervalIntegral.integral_nonneg (by unfold curvePeriod; positivity)
  intro x _
  apply mul_nonneg
  · exact (((G.product circumference h).flow.metric t).toRiemannianMetric.toCore
      ((C.solutions circumference h).curve z x t)).re_inner_nonneg _
  · exact Real.sqrt_nonneg _

/-- Equation (19.9), p. 455: for every member and circle circumference below
one, the times where the curvature energy exceeds B have measure at most
the same family constant divided by B. -/
theorem m65FamilyEnergy_badTimes_measure_le
    (C : M63FamilyConclusion G Gamma zeta) (E : M64AppliedFamilyEstimates G C)
    (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) {B : ℝ} (hB : 0 < B) :
    volume.real {t | t ∈ Set.Icc a b ∧ B < m65FamilyEnergy C circumference h z t} ≤
      ((m63FamilyLengthSup (F.metric a) Gamma + 1) * Real.exp (G.K2 * (b - a))) / B := by
  have hab : a ≤ b := by
    obtain ⟨t, ht⟩ := F.nontrivial.nonempty
    exact ht.1.trans ht.2
  exact M65.energy_badTimes_measure_le hab
    (m65FamilyEnergy_nonneg C circumference h z)
    (m64FamilyEnergyIntegrable C E circumference h z)
    (m64FamilyEnergyBound C E circumference h hlt z) hB

end PoincareMT
