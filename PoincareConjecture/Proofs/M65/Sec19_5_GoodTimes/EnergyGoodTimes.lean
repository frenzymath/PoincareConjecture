import PoincareConjecture.Proofs.M64.FamilyAdapters
import PoincareConjecture.Proofs.M65.Mathlib.EnergyBadTimes

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral
open MeasureTheory

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta : ℝ}

noncomputable def m65FamilyEnergy (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod,
    m62CurvatureSquared (G.product circumference h).flow
      ((C.solutions circumference h).curve z) t x *
      curveSpeed (G.product circumference h).flow
        ((C.solutions circumference h).curve z) t x

theorem m65FamilyEnergy_nonneg (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) (t : ℝ) :
    0 ≤ m65FamilyEnergy C circumference h z t := by
  apply intervalIntegral.integral_nonneg (by unfold curvePeriod; positivity)
  intro x _
  apply mul_nonneg
  · exact (((G.product circumference h).flow.metric t).toRiemannianMetric.toCore
      ((C.solutions circumference h).curve z x t)).re_inner_nonneg _
  · exact Real.sqrt_nonneg _

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

end PoincareConjecture
