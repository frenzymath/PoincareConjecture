import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

noncomputable local instance withinRicciBilinearNorm (n : ℕ) :
    NormedAddCommGroup (SpacetimeBounds.MetricCoefficient n) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance withinRicciBilinearSpace (n : ℕ) :
    NormedSpace ℝ (SpacetimeBounds.MetricCoefficient n) :=
  ContinuousLinearMap.toNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option maxHeartbeats 800000 in

theorem hasDerivWithinAt_pullbackCoefficients_ricci
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    HasDerivWithinAt (fun s => (F.metric s).pullbackCoefficients e x)
      (SpacetimeBounds.ricciFlowOperator n
        (SpacetimeBounds.metricTwoJet ((F.metric t).pullbackCoefficients e) x)) J t := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hscalar (i j : Fin n) :
      HasDerivWithinAt (fun s => (F.metric s).pullbackCoefficients e x (b i) (b j))
        (-2 * SpacetimeBounds.jetRicci
          (SpacetimeBounds.metricTwoJet ((F.metric t).pullbackCoefficients e) x) (b i) (b j))
        J t := by
    rw [SpacetimeBounds.jetRicci_metricTwoJet_pullback (F.connection t) hU he hi hx]
    exact F.equation t ht (e x) _ _
  have hsum := HasDerivWithinAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivWithinAt.sum (u := Finset.univ) (fun j _ =>
      (hscalar i j).smul_const ((innerSL ℝ (b i)).smulRight (innerSL ℝ (b j)))))
  have hfun : (∑ i, ∑ j, fun s =>
      ((F.metric s).pullbackCoefficients e x (b i) (b j)) •
        (innerSL ℝ (b i)).smulRight (innerSL ℝ (b j))) =
        (fun s => (F.metric s).pullbackCoefficients e x) := by
    funext s
    simp only [Finset.sum_apply]
    exact (SpacetimeBounds.bilinear_eq_sum_dual b
      ((F.metric s).pullbackCoefficients e x)).symm
  rw [hfun] at hsum
  exact hsum

end PoincareConjecture.M44
