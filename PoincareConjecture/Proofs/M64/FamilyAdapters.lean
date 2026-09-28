import PoincareConjecture.Statements.M64Approximation
import PoincareConjecture.Proofs.M63.Adapters













set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta : ℝ}




theorem m64AppliedFamilyEstimates_from_M63
    (analytic : M63AnalyticConclusion F G) (C : M63FamilyConclusion G Gamma zeta) :
    M64AppliedFamilyEstimates G C := by
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hst⟩ := F.nontrivial.exists_lt
    exact lt_of_le_of_lt hs.1 (lt_of_lt_of_le hst ht.2)
  exact ⟨fun circumference h z =>
    analytic.product_estimates circumference h b hab le_rfl
      ((C.solutions circumference h).curve z)
      (m63C2_of_m62 ((C.solutions circumference h).shrinking z))⟩




theorem m64EvolvingApproximation_from_M63
    [T2Space M] [SecondCountableTopology M]
    (hM63 : M63RampEstimatesTheory.{u})
    (compact : IsCompact (Set.univ : Set M))
    (analytic : M63AnalyticConclusion F G)
    (null_family : M61NullFamily Gamma) (hzeta : 0 < zeta)
    {N : ℕ}
    (raw : M64RawFamilyApproximation (F.metric a) (F.connection a) Gamma zeta)
    (count_eq : raw.count = N) :
    Nonempty (M64EvolvingApproximation G Gamma zeta N) := by
  obtain ⟨C, hC⟩ := hM63.2.2.2 M a b F compact G Gamma null_family zeta hzeta raw.toM63
  exact ⟨{ raw := raw
           count_eq := count_eq
           family := C
           approximation_eq := hC
           estimates := m64AppliedFamilyEstimates_from_M63 analytic C }⟩





theorem m64FamilyInitialLength (C : M63FamilyConclusion G Gamma zeta)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) :
    m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) a =
      m62Length (G.product circumference h).flow
        (fun x _ => m63CanonicalRamp (G.product circumference h)
          (periodicFreeLoop (C.approximation.family z)) x) a := by
  exact congrArg
    (fun gamma : ℝ → (G.product circumference h).charts.Point =>
      ∫ x in (0 : ℝ)..curvePeriod,
        ((G.product circumference h).flow.metric a).tangentNorm (gamma x)
          (curveVelocity (n := 3 + 1) gamma x))
    (funext ((C.solutions circumference h).initial_eq z))




theorem m64FamilyEnergyIntegrable (C : M63FamilyConclusion G Gamma zeta)
    (E : M64AppliedFamilyEstimates G C)
    (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) :
    IntervalIntegrable
      (fun t => ∫ x in (0 : ℝ)..curvePeriod,
        m62CurvatureSquared (G.product circumference h).flow
          ((C.solutions circumference h).curve z) t x *
          curveSpeed (G.product circumference h).flow
            ((C.solutions circumference h).curve z) t x)
      MeasureTheory.volume a b :=
  (E.curve_estimates circumference h z).energy_integrable




theorem m64FamilyEnergyBound (C : M63FamilyConclusion G Gamma zeta)
    (E : M64AppliedFamilyEstimates G C)
    (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
    (z : LoopTwoSphere) :
    (∫ t in a..b, ∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared (G.product circumference h).flow
        ((C.solutions circumference h).curve z) t x *
        curveSpeed (G.product circumference h).flow
          ((C.solutions circumference h).curve z) t x) ≤
      (m63FamilyLengthSup (F.metric a) Gamma + 1) * Real.exp (G.K2 * (b - a)) := by
  have h_initial : m62Length (G.product circumference h).flow
      ((C.solutions circumference h).curve z) a ≤
        m63FamilyLengthSup (F.metric a) Gamma + 1 :=
    (m64FamilyInitialLength C circumference h z).trans_le
      (C.canonical_length circumference h hlt z)
  exact (E.curve_estimates circumference h z).energy_bound.trans
    (mul_le_mul_of_nonneg_right h_initial (Real.exp_nonneg _))

end PoincareConjecture
