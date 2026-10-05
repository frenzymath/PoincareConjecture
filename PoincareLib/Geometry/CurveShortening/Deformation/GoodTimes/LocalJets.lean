import PoincareLib.Geometry.CurveShortening.Deformation.GoodTimes.EnergyGoodTimes
import PoincareLib.Geometry.CurveShortening.Deformation.GoodTimes.SubarcEnergy

/-!
# Local derivative bounds at actual energy-good times

Morgan--Tian Lemma 19.24 and the following construction, printed pp. 455-456, with the
2015 correction, p. 9. Both initial length and initial total curvature
are checked against the selected family's retained bound before applying
the derivative service. No new circumference-dependent constant is chosen.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta : ℝ}

/-- The exact initial angular map identifies total curvature as well as
length, retaining the initial-data dependence required by correction p. 9. -/
theorem m65FamilyInitialTotalCurvature (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) :
    m62TotalCurvature (G.product circumference h).flow
      ((C.solutions circumference h).curve z) a =
      m62TotalCurvature (G.product circumference h).flow
        (fun x _ => m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (C.approximation.family z)) x) a := by
  exact congrArg
    (fun gamma : ℝ → (G.product circumference h).charts.Point =>
      m62TotalCurvature (G.product circumference h).flow (fun x _ => gamma x) a)
    (funext ((C.solutions circumference h).initial_eq z))

/-- Corrected Lemma 19.24 applied to the exact family at an energy-good
reference time; the window and length conditions are those of p. 455. -/
theorem m65FamilyJets_of_energy_le (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) {s r B : ℝ} (hs : s ∈ Set.Ioo a b)
    (hr : 0 < r) (hr1 : r < 1)
    (hwindow : s + (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) *
      r ^ 2 < b)
    (hlength : r ≤ m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) s)
    (henergy : m65FamilyEnergy C circumference h z s ≤ B)
    (hscale : r * B ≤
      (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) ^ 2) :
    ∀ t ∈ Set.Ioo s
        (s + (C.derivative_estimates.delta0 * C.derivative_estimates.radius0 ^ 2) * r ^ 2),
      ∀ i x, m63CurvatureJetSquared (G.product circumference h).flow
        ((C.solutions circumference h).curve z) i t x ≤
          C.derivative_estimates.constant i / (t - s) ^ (i + 1) := by
  have hL : m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) a ≤ C.initial_bound :=
    (m64FamilyInitialLength C circumference h z).trans_le
      ((C.canonical_length circumference h hlt z).trans C.initial_length_bound)
  have hTheta : m62TotalCurvature (G.product circumference h).flow
      ((C.solutions circumference h).curve z) a ≤ C.initial_bound :=
    (m65FamilyInitialTotalCurvature C circumference h z).trans_le
      ((C.canonical_total_curvature circumference h z).trans C.initial_turning_bound)
  exact C.derivative_estimates.all_derivatives circumference h hlt _
    (m63C2_of_m62 ((C.solutions circumference h).shrinking z)) hL hTheta
    s r hs.1.le hr hr1 hwindow hlength
    (m65SmallSubarcs_of_energy_le _ _ ((C.solutions circumference h).shrinking z)
      hs hr.le (mul_nonneg C.derivative_estimates.delta0_positive.le (sq_nonneg _))
      henergy hscale)

end PoincareMT
