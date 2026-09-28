import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.EnergyGoodTimes
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.SubarcEnergy










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta : ℝ}



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

end PoincareConjecture
