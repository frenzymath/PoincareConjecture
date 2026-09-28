import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.SlopeCollapse
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ProjectedTangent
import PoincareConjecture.Statements.M63RampEstimates










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {G : M63AmbientGeometry F}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}



theorem m65FamilySlope_uniform_small (C : M63FamilyConclusion G Gamma zeta)
    {ell K : ℝ} (hell : 0 < ell) (hK : 0 ≤ K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ circumference (h : 0 < circumference),
      circumference < delta → ∀ z : LoopTwoSphere, ∀ J : Set ℝ,
      J ⊆ Icc a b →
      (∀ t ∈ J, ell ≤ m62Length (G.product circumference h).flow
        ((C.solutions circumference h).curve z) t) →
      (∀ t ∈ J, ∀ x, m62Curvature (G.product circumference h).flow
        ((C.solutions circumference h).curve z) t x ≤ K) →
      ∀ t ∈ J, ∀ x,
        |m62Slope (G.product circumference h)
          ((C.solutions circumference h).curve z) t x| < epsilon := by
  have hcont : ContinuousAt (fun r : ℝ => (r / ell) ^ 2 + 2 * K * r) 0 := by
    fun_prop
  have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ), (r / ell) ^ 2 + 2 * K * r < epsilon ^ 2 := by
    apply hcont.eventually_lt continuousAt_const
    simpa using sq_pos_of_pos hepsilon
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨delta, hdelta, ?_⟩
  intro circumference h hlt z J hJ hlength hcurv t ht x
  have hbound : (circumference / ell) ^ 2 + 2 * K * circumference < epsilon ^ 2 :=
    hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_pos h] using hlt)
  obtain ⟨L, hdegree⟩ := (C.solutions circumference h).degree_one z t (hJ ht)
  have hsquare := m65Slope_sq_le_circumference (G.product circumference h)
    ((C.solutions circumference h).curve z) ((C.solutions circumference h).shrinking z)
    (hJ ht) hell (hlength t ht) hK
    (fun y => ((C.solutions circumference h).ramp z t (hJ ht) y).le)
    (hcurv t ht) L hdegree x
  exact abs_lt_of_sq_lt_sq (hsquare.trans_lt hbound) hepsilon.le



theorem m65FamilyProjected_immersed_small (C : M63FamilyConclusion G Gamma zeta)
    {ell K : ℝ} (hell : 0 < ell) (hK : 0 ≤ K) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ circumference (h : 0 < circumference),
      circumference < delta → ∀ z : LoopTwoSphere, ∀ J : Set ℝ,
      J ⊆ Icc a b →
      (∀ t ∈ J, ell ≤ m62Length (G.product circumference h).flow
        ((C.solutions circumference h).curve z) t) →
      (∀ t ∈ J, ∀ x, m62Curvature (G.product circumference h).flow
        ((C.solutions circumference h).curve z) t x ≤ K) →
      ∀ t ∈ J, ∀ x, curveVelocity (n := 3)
        (fun y => ((C.solutions circumference h).curve z y t).1) x ≠ 0 := by
  obtain ⟨delta, hdelta, hslope⟩ := m65FamilySlope_uniform_small C hell hK 1 zero_lt_one
  refine ⟨delta, hdelta, ?_⟩
  intro circumference h hlt z J hJ hlength hcurv t ht x
  exact m65Projection_immersed_of_slope_lt_one (G.product circumference h)
    ((C.solutions circumference h).curve z) ((C.solutions circumference h).shrinking z)
    (hJ ht) x (hslope circumference h hlt z J hJ hlength hcurv t ht x)

end PoincareConjecture
